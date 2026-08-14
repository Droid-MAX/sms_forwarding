#include "idf_lpa.h"

#include <ctype.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#include <algorithm>
#include <array>
#include <limits>
#include <utility>

#include "esp_crt_bundle.h"
#include "esp_heap_caps.h"
#include "esp_http_client.h"
#include "idf_esim_codec.h"
#include "idf_esim_lpa.h"
#include "idf_log.h"
#include "idf_modem.h"
#include "mbedtls/base64.h"
#include "psa/crypto.h"

namespace {

static constexpr size_t kMaxActivationCodeLength = 512;
static constexpr size_t kActivationPrefixLength = 4;
static constexpr size_t kMaxInputLength = kMaxActivationCodeLength + kActivationPrefixLength;
static constexpr size_t kMaxMatchingIdLength = 128;
static constexpr size_t kMaxHostLength = 253;
static constexpr size_t kMaxOptionalFieldLength = 64;
static constexpr size_t kMaxCoreFields = 3;
static constexpr size_t kMaxStoredExtensions = 4;
static constexpr size_t kMaxActivationFields = kMaxCoreFields + kMaxStoredExtensions;

static void clear_string(std::string& value)
{
    // move 后的 std::string 可能 size() 已为 0，但其 SSO/容量区域仍保留旧字节；
    // 先把逻辑长度扩到现有容量，再统一清零，尽量覆盖这些短期残留。
    const size_t capacity = value.capacity();
    if (capacity > value.size()) value.resize(capacity, '\0');
    if (!value.empty()) {
        volatile unsigned char* bytes = reinterpret_cast<volatile unsigned char*>(value.data());
        for (size_t i = 0; i < value.size(); ++i) bytes[i] = 0;
    }
    value.clear();
    std::string().swap(value);
}

class SensitiveText {
public:
    SensitiveText() = default;
    SensitiveText(const SensitiveText&) = delete;
    SensitiveText& operator=(const SensitiveText&) = delete;
    ~SensitiveText() { clear_string(text); }

    void assign(const std::string& source, size_t offset, size_t length)
    {
        text.assign(source.data() + offset, length);
    }

    std::string text;
};

class SensitiveFields {
public:
    SensitiveFields() = default;
    SensitiveFields(const SensitiveFields&) = delete;
    SensitiveFields& operator=(const SensitiveFields&) = delete;
    ~SensitiveFields()
    {
        for (std::string& field : values) clear_string(field);
        std::vector<std::string>().swap(values);
    }

    std::vector<std::string> values;
};

static void trim_ascii_bounds(const std::string& value, size_t& begin, size_t& end)
{
    begin = 0;
    while (begin < value.size() && isspace(static_cast<unsigned char>(value[begin]))) ++begin;
    end = value.size();
    while (end > begin && isspace(static_cast<unsigned char>(value[end - 1]))) --end;
}

static bool is_printable_ascii(const std::string& value)
{
    for (unsigned char ch : value) {
        if (ch < 0x20U || ch > 0x7EU) return false;
    }
    return true;
}

static bool valid_matching_id(const std::string& value, std::string& message)
{
    if (value.empty()) {
        message = "MatchingID 不能为空";
        return false;
    }
    if (value.size() > kMaxMatchingIdLength) {
        message = "MatchingID 超过 128 字符";
        return false;
    }
    for (unsigned char ch : value) {
        if (ch < 0x21U || ch > 0x7EU || ch == '$') {
            message = "MatchingID 包含非法字符";
            return false;
        }
    }
    return true;
}

static bool valid_rsp_matching_id(const std::string& value, std::string& message)
{
    if (!valid_matching_id(value, message)) return false;
    for (unsigned char ch : value) {
        if (!((ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch == '-')) {
            message = "MatchingID 不符合 SGP.22 字符规则";
            return false;
        }
    }
    return true;
}

static bool valid_smdp_host(const std::string& value, std::string& message)
{
    if (value.empty()) {
        message = "SM-DP+ 主机不能为空";
        return false;
    }
    if (value.size() > kMaxHostLength) {
        message = "SM-DP+ 主机过长";
        return false;
    }

    size_t label_start = 0;
    size_t label_count = 0;
    bool all_numeric_labels = true;
    while (label_start <= value.size()) {
        size_t dot = value.find('.', label_start);
        size_t label_end = dot == std::string::npos ? value.size() : dot;
        size_t label_len = label_end - label_start;
        if (label_len == 0 || label_len > 63U) {
            message = "SM-DP+ 主机包含空标签或过长标签";
            return false;
        }
        if (value[label_start] == '-' || value[label_end - 1U] == '-') {
            message = "SM-DP+ 主机标签不能以连字符开头或结尾";
            return false;
        }
        bool numeric_label = true;
        for (size_t i = label_start; i < label_end; ++i) {
            unsigned char ch = static_cast<unsigned char>(value[i]);
            if (!((ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z') ||
                  (ch >= '0' && ch <= '9') || ch == '-')) {
                message = "SM-DP+ 主机必须是 ASCII FQDN，不能包含 scheme、路径或端口";
                return false;
            }
            if (ch < '0' || ch > '9') numeric_label = false;
        }
        all_numeric_labels = all_numeric_labels && numeric_label;
        ++label_count;
        if (dot == std::string::npos) break;
        label_start = dot + 1U;
    }

    if (label_count < 2U) {
        message = "SM-DP+ 主机必须是完整 FQDN";
        return false;
    }
    if (all_numeric_labels) {
        message = "SM-DP+ 主机不接受数字地址";
        return false;
    }
    return true;
}

static bool split_fields(const std::string& value, SensitiveFields& fields)
{
    size_t start = 0;
    while (start <= value.size()) {
        size_t delimiter = value.find('$', start);
        size_t end = delimiter == std::string::npos ? value.size() : delimiter;
        if (fields.values.size() >= kMaxActivationFields) return false;
        fields.values.emplace_back(value.data() + start, end - start);
        if (delimiter == std::string::npos) break;
        start = delimiter + 1U;
    }
    return true;
}

static constexpr size_t kMaxEs9JsonBody = 24U * 1024U;
static constexpr size_t kMaxEs9Object = 8U * 1024U;
static constexpr uint32_t kMinimumValidEpoch = 1700000000U;
static constexpr uint32_t kEs9TimeoutMs = 15000U;

static void clear_sensitive_bytes(std::vector<uint8_t>& value)
{
    if (!value.empty()) {
        volatile uint8_t* bytes = value.data();
        for (size_t i = 0; i < value.size(); ++i) bytes[i] = 0;
    }
    std::vector<uint8_t>().swap(value);
}

class SensitiveBytes {
public:
    SensitiveBytes() = default;
    SensitiveBytes(const SensitiveBytes&) = delete;
    SensitiveBytes& operator=(const SensitiveBytes&) = delete;
    ~SensitiveBytes() { clear_sensitive_bytes(value); }

    std::vector<uint8_t> value;
};

static bool equal_ascii_ci(const std::string& left, const char* right)
{
    if (!right || left.size() != strlen(right)) return false;
    for (size_t i = 0; i < left.size(); ++i) {
        if (tolower(static_cast<unsigned char>(left[i])) !=
            tolower(static_cast<unsigned char>(right[i]))) {
            return false;
        }
    }
    return true;
}

static std::string lower_ascii_copy(const std::string& value)
{
    std::string out = value;
    for (char& ch : out) ch = static_cast<char>(tolower(static_cast<unsigned char>(ch)));
    return out;
}

static void append_json_string(std::string& out, const std::string& value)
{
    out.push_back('"');
    for (unsigned char ch : value) {
        switch (ch) {
            case '"': out += "\\\""; break;
            case '\\': out += "\\\\"; break;
            case '\b': out += "\\b"; break;
            case '\f': out += "\\f"; break;
            case '\n': out += "\\n"; break;
            case '\r': out += "\\r"; break;
            case '\t': out += "\\t"; break;
            default:
                if (ch < 0x20U) {
                    char buf[7];
                    snprintf(buf, sizeof(buf), "\\u%04X", static_cast<unsigned>(ch));
                    out += buf;
                } else {
                    out.push_back(static_cast<char>(ch));
                }
                break;
        }
    }
    out.push_back('"');
}

static void append_json_field(std::string& out,
                              const char* key,
                              const std::string& value,
                              bool& first)
{
    if (!first) out.push_back(',');
    first = false;
    append_json_string(out, key);
    out.push_back(':');
    append_json_string(out, value);
}

struct Es9HttpCapture {
    std::string body;
    std::string adminProtocol;
    bool adminProtocolSeen = false;
    bool bodyOverflow = false;
    size_t responseBytes = 0;

    ~Es9HttpCapture() { clear_string(body); }
};

struct Es9HttpDiagnostics {
    int transportErrno = 0;
    int tlsCode = 0;
    int tlsFlags = 0;
    esp_err_t tlsError = ESP_OK;
};

static Es9HttpDiagnostics collect_es9_http_diagnostics(esp_http_client_handle_t client)
{
    Es9HttpDiagnostics diagnostics;
    if (client) {
        diagnostics.transportErrno = esp_http_client_get_errno(client);
        diagnostics.tlsError = esp_http_client_get_and_clear_last_tls_error(
            client, &diagnostics.tlsCode, &diagnostics.tlsFlags);
    }
    return diagnostics;
}

static void set_es9_http_error(std::string& message,
                               const char* operation,
                               esp_err_t error,
                               int status_code,
                               const Es9HttpDiagnostics& diagnostics)
{
    const char* errno_text = diagnostics.transportErrno > 0
        ? strerror(diagnostics.transportErrno)
        : "none";
    char buffer[320];
    snprintf(buffer, sizeof(buffer),
             "ES9+ %s HTTPS 请求失败（err=%s/0x%08X，errno=%d/%s，tls=%s/0x%08X，tlsCode=0x%08X，flags=0x%08X，HTTP=%d）",
             operation ? operation : "请求",
             esp_err_to_name(error), static_cast<unsigned>(error),
             diagnostics.transportErrno, errno_text,
             esp_err_to_name(diagnostics.tlsError), static_cast<unsigned>(diagnostics.tlsError),
             static_cast<unsigned>(diagnostics.tlsCode),
             static_cast<unsigned>(diagnostics.tlsFlags), status_code);
    message = buffer;
}

static esp_err_t es9_http_event_handler(esp_http_client_event_t* event)
{
    if (!event || !event->user_data) return ESP_OK;
    Es9HttpCapture* capture = static_cast<Es9HttpCapture*>(event->user_data);
    if (event->event_id == HTTP_EVENT_ON_HEADER && event->header_key) {
        if (equal_ascii_ci(event->header_key, "X-Admin-Protocol")) {
            capture->adminProtocolSeen = true;
            capture->adminProtocol.assign(event->header_value ? event->header_value : "");
        }
    } else if (event->event_id == HTTP_EVENT_ON_DATA && event->data && event->data_len > 0) {
        size_t data_len = static_cast<size_t>(event->data_len);
        if (data_len > std::numeric_limits<size_t>::max() - capture->responseBytes) {
            capture->responseBytes = std::numeric_limits<size_t>::max();
        } else {
            capture->responseBytes += data_len;
        }
        if (data_len > kMaxEs9JsonBody ||
            capture->body.size() > kMaxEs9JsonBody - data_len) {
            capture->bodyOverflow = true;
            return ESP_OK;
        }
        capture->body.append(static_cast<const char*>(event->data), data_len);
    }
    return ESP_OK;
}

static bool valid_rsp_protocol(const std::string& protocol)
{
    return protocol.rfind("gsma/rsp/v2.", 0) == 0 && protocol.size() <= 32U;
}

static const char* rsp_protocol_state(const std::string& protocol, bool seen)
{
    if (!seen) return "missing";
    return valid_rsp_protocol(protocol) ? "valid" : "invalid";
}

static void log_es9_http_summary(const char* operation,
                                 esp_err_t error,
                                 int status_code,
                                 size_t body_bytes,
                                 bool body_overflow,
                                 const std::string& protocol,
                                 bool protocol_seen,
                                 const Es9HttpDiagnostics& diagnostics)
{
    const char* op = operation ? operation : "请求";
    const char* protocol_state = rsp_protocol_state(protocol, protocol_seen);
    if (error == ESP_OK) {
        idf_logf("ES9+ %s: HTTP=%d err=%s/0x%08X bodyBytes=%u overflow=%d protocol=%s",
                 op, status_code, esp_err_to_name(error), static_cast<unsigned>(error),
                 static_cast<unsigned>(body_bytes), body_overflow ? 1 : 0, protocol_state);
        return;
    }
    idf_logf("ES9+ %s: HTTP=%d err=0x%08X bytes=%u ov=%d proto=%s errno=%d tls=0x%08X code=0x%08X flags=0x%08X",
             op, status_code, static_cast<unsigned>(error),
             static_cast<unsigned>(body_bytes), body_overflow ? 1 : 0, protocol_state,
             diagnostics.transportErrno, static_cast<unsigned>(diagnostics.tlsError),
             static_cast<unsigned>(diagnostics.tlsCode),
             static_cast<unsigned>(diagnostics.tlsFlags));
}

static bool check_rsp_protocol(const std::string& protocol,
                               bool protocol_seen,
                               bool allow_missing_protocol,
                               const char* operation,
                               std::string& message)
{
    if (valid_rsp_protocol(protocol)) return true;
    if (protocol_seen) {
        message = "ES9+ X-Admin-Protocol 无效";
        return false;
    }
    if (!allow_missing_protocol) {
        message = "ES9+ 响应缺少 X-Admin-Protocol";
        return false;
    }
    idf_logf("ES9+ %s 响应缺少 X-Admin-Protocol，已按兼容模式继续解析",
             operation ? operation : "请求");
    return true;
}

static esp_err_t es9_post_json(const std::string& host,
                               const char* operation,
                               bool allow_missing_protocol,
                               const char* path,
                               const std::string& request_body,
                               std::string& response_body,
                               std::string& message)
{
    response_body.clear();
    uint32_t now = static_cast<uint32_t>(time(nullptr));
    if (now < kMinimumValidEpoch) {
        message = "设备时间未同步，不能连接 SM-DP+";
        return ESP_ERR_INVALID_STATE;
    }
    if (host.empty() || host.size() > kMaxHostLength || !path || request_body.empty() ||
        request_body.size() > kMaxEs9JsonBody) {
        message = "ES9+ 请求参数或大小无效";
        return ESP_ERR_INVALID_ARG;
    }

    std::string url;
    url.reserve(8U + host.size() + strlen(path));
    url = "https://";
    url += host;
    url += path;

    Es9HttpCapture capture;
    esp_http_client_config_t config = {};
    config.url = url.c_str();
    config.timeout_ms = static_cast<int>(kEs9TimeoutMs);
    config.crt_bundle_attach = esp_crt_bundle_attach;
    config.skip_cert_common_name_check = false;
    config.keep_alive_enable = false;
    config.disable_auto_redirect = true;
    config.buffer_size = 2048;
    size_t tx_size = request_body.size() + 512U;
    config.buffer_size_tx = static_cast<int>(std::min<size_t>(32768U, std::max<size_t>(2048U, tx_size)));
    config.event_handler = es9_http_event_handler;
    config.user_data = &capture;

    esp_http_client_handle_t client = esp_http_client_init(&config);
    if (!client) {
        message = "ES9+ HTTPS 客户端内存不足";
        return ESP_ERR_NO_MEM;
    }

    esp_err_t err = esp_http_client_set_method(client, HTTP_METHOD_POST);
    if (err == ESP_OK) err = esp_http_client_set_header(client, "Content-Type", "application/json");
    if (err == ESP_OK) err = esp_http_client_set_header(client, "User-Agent", "gsma-rsp-lpad");
    if (err == ESP_OK) {
        err = esp_http_client_set_header(client, "X-Admin-Protocol", "gsma/rsp/v2.7.0");
    }
    if (err == ESP_OK) {
        err = esp_http_client_set_post_field(client, request_body.data(), request_body.size());
    }
    if (err == ESP_OK) {
        err = esp_http_client_perform(client);
    }
    int status_code = esp_http_client_get_status_code(client);
    Es9HttpDiagnostics diagnostics = collect_es9_http_diagnostics(client);
    log_es9_http_summary(operation, err, status_code, capture.responseBytes,
                         capture.bodyOverflow, capture.adminProtocol,
                         capture.adminProtocolSeen, diagnostics);
    esp_http_client_cleanup(client);

    if (capture.bodyOverflow) {
        message = "ES9+ 响应超过大小上限";
        return ESP_ERR_INVALID_SIZE;
    }
    if (err != ESP_OK) {
        set_es9_http_error(message, operation, err, status_code, diagnostics);
        return err;
    }
    if (status_code != 200) {
        char buf[64];
        snprintf(buf, sizeof(buf), "ES9+ HTTP 状态异常（%d）", status_code);
        message = buf;
        return ESP_ERR_INVALID_RESPONSE;
    }
    if (!check_rsp_protocol(capture.adminProtocol, capture.adminProtocolSeen,
                             allow_missing_protocol, operation, message)) {
        return ESP_ERR_INVALID_RESPONSE;
    }
    if (capture.body.empty()) {
        message = "ES9+ 响应为空";
        return ESP_ERR_INVALID_RESPONSE;
    }
    response_body = std::move(capture.body);
    return ESP_OK;
}

static bool json_decode_string(const std::string& json,
                               size_t start,
                               std::string& out,
                               size_t& end)
{
    out.clear();
    if (start >= json.size() || json[start] != '"') return false;
    for (size_t i = start + 1U; i < json.size(); ++i) {
        unsigned char ch = static_cast<unsigned char>(json[i]);
        if (ch == '"') {
            end = i + 1U;
            return true;
        }
        if (ch == '\\') {
            if (++i >= json.size()) return false;
            switch (json[i]) {
                case '"': out.push_back('"'); break;
                case '\\': out.push_back('\\'); break;
                case '/': out.push_back('/'); break;
                case 'b': out.push_back('\b'); break;
                case 'f': out.push_back('\f'); break;
                case 'n': out.push_back('\n'); break;
                case 'r': out.push_back('\r'); break;
                case 't': out.push_back('\t'); break;
                default: return false;
            }
        } else {
            if (ch < 0x20U) return false;
            out.push_back(static_cast<char>(ch));
        }
        if (out.size() > kMaxEs9JsonBody) return false;
    }
    return false;
}

static bool json_get_string(const std::string& json,
                            const char* key,
                            std::string& out,
                            bool required)
{
    out.clear();
    if (!key) return false;
    std::string needle = "\"";
    needle += key;
    needle += "\"";
    size_t pos = 0;
    size_t count = 0;
    SensitiveText candidate;
    while ((pos = json.find(needle, pos)) != std::string::npos) {
        size_t cursor = pos + needle.size();
        while (cursor < json.size() && isspace(static_cast<unsigned char>(json[cursor]))) ++cursor;
        if (cursor >= json.size() || json[cursor] != ':') {
            pos += needle.size();
            continue;
        }
        ++cursor;
        while (cursor < json.size() && isspace(static_cast<unsigned char>(json[cursor]))) ++cursor;
        size_t end = 0;
        if (!json_decode_string(json, cursor, candidate.text, end)) return false;
        ++count;
        if (count > 1U) return false;
        out = candidate.text;
        pos = end;
    }
    return required ? count == 1U : count <= 1U;
}

static bool base64_text_valid(const std::string& text)
{
    if (text.empty() || (text.size() % 4U) != 0U) return false;
    size_t padding = 0;
    for (size_t i = 0; i < text.size(); ++i) {
        unsigned char ch = static_cast<unsigned char>(text[i]);
        bool alphabet = (ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z') ||
                        (ch >= '0' && ch <= '9') || ch == '+' || ch == '/';
        if (ch == '=') {
            if (i + 2U < text.size()) return false;
            ++padding;
            continue;
        }
        if (!alphabet || padding != 0U) return false;
    }
    return padding <= 2U;
}

static bool base64_decode_bounded(const std::string& text,
                                  size_t max_size,
                                  std::vector<uint8_t>& out,
                                  std::string& message)
{
    out.clear();
    if (!base64_text_valid(text)) {
        message = "ES9+ Base64 字段格式无效";
        return false;
    }
    size_t capacity = (text.size() / 4U) * 3U;
    if (text.size() >= 2U && text[text.size() - 1U] == '=') --capacity;
    if (text.size() >= 2U && text[text.size() - 2U] == '=') --capacity;
    if (capacity > max_size) {
        message = "ES9+ Base64 字段超过大小上限";
        return false;
    }
    out.assign(capacity + 1U, 0);
    size_t decoded = 0;
    int rc = mbedtls_base64_decode(out.data(), out.size(), &decoded,
                                   reinterpret_cast<const unsigned char*>(text.data()),
                                   text.size());
    if (rc != 0 || decoded > max_size) {
        out.clear();
        message = "ES9+ Base64 解码失败";
        return false;
    }
    out.resize(decoded);
    return true;
}

static bool base64_encode_bytes(const std::vector<uint8_t>& input,
                                std::string& out,
                                std::string& message)
{
    out.clear();
    size_t capacity = ((input.size() + 2U) / 3U) * 4U + 1U;
    out.assign(capacity, '\0');
    size_t encoded = 0;
    int rc = mbedtls_base64_encode(reinterpret_cast<unsigned char*>(out.data()), out.size(),
                                   &encoded, input.data(), input.size());
    if (rc != 0) {
        out.clear();
        message = "ES9+ Base64 编码失败";
        return false;
    }
    out.resize(encoded);
    return true;
}

static int hex_value(unsigned char ch)
{
    if (ch >= '0' && ch <= '9') return ch - '0';
    if (ch >= 'A' && ch <= 'F') return ch - 'A' + 10;
    if (ch >= 'a' && ch <= 'f') return ch - 'a' + 10;
    return -1;
}

static bool decode_transaction_id(const std::string& text,
                                  std::vector<uint8_t>& out,
                                  std::string& message)
{
    out.clear();
    if (text.size() < 2U || text.size() > 32U || (text.size() % 2U) != 0U) {
        message = "ES9+ transactionId 长度无效";
        return false;
    }
    out.reserve(text.size() / 2U);
    for (size_t i = 0; i < text.size(); i += 2U) {
        int high = hex_value(static_cast<unsigned char>(text[i]));
        int low = hex_value(static_cast<unsigned char>(text[i + 1U]));
        if (high < 0 || low < 0) {
            out.clear();
            message = "ES9+ transactionId 不是合法 HEX";
            return false;
        }
        out.push_back(static_cast<uint8_t>((high << 4) | low));
    }
    return true;
}

static const idf_esim_internal::Tlv* unique_child(const idf_esim_internal::Tlv& parent,
                                                  const uint8_t* tag,
                                                  size_t tag_len,
                                                  bool& duplicate)
{
    duplicate = false;
    const idf_esim_internal::Tlv* found = nullptr;
    for (const idf_esim_internal::Tlv& child : parent.children) {
        if (!idf_esim_internal::tag_is(child, tag, tag_len)) continue;
        if (found) {
            duplicate = true;
            return nullptr;
        }
        found = &child;
    }
    return found;
}

static std::string safe_tlv_shape(const idf_esim_internal::Tlv& parent)
{
    std::string shape;
    constexpr size_t kMaxChildren = 8;
    for (size_t i = 0; i < parent.children.size() && i < kMaxChildren; ++i) {
        if (!shape.empty()) shape.push_back('/');
        const idf_esim_internal::Tlv& child = parent.children[i];
        for (uint8_t byte : child.tag) {
            char part[4];
            snprintf(part, sizeof(part), "%02X", static_cast<unsigned>(byte));
            shape += part;
        }
        char length[24];
        snprintf(length, sizeof(length), ":%u",
                 static_cast<unsigned>(child.value.size()));
        shape += length;
    }
    if (parent.children.size() > kMaxChildren) shape += "/...";
    return shape.empty() ? std::string("empty") : shape;
}

static void clear_tlv_sensitive(idf_esim_internal::Tlv& tlv)
{
    for (idf_esim_internal::Tlv& child : tlv.children) clear_tlv_sensitive(child);
    if (!tlv.value.empty()) {
        volatile uint8_t* bytes = tlv.value.data();
        for (size_t i = 0; i < tlv.value.size(); ++i) bytes[i] = 0;
    }
    std::vector<uint8_t>().swap(tlv.value);
    std::vector<idf_esim_internal::Tlv>().swap(tlv.children);
}

class SensitiveTlv {
public:
    ~SensitiveTlv() { clear_tlv_sensitive(value); }
    idf_esim_internal::Tlv value;
};

static bool validate_server_signed1(const std::vector<uint8_t>& encoded,
                                    const std::vector<uint8_t>& transaction_id,
                                    const std::array<uint8_t, 16>& euicc_challenge,
                                    const std::string& host,
                                    std::string& message)
{
    if (encoded.empty() || encoded.size() > kMaxEs9Object) {
        message = "ES9+ serverSigned1 大小无效";
        return false;
    }
    SensitiveTlv root_holder;
    idf_esim_internal::Tlv& root = root_holder.value;
    if (!idf_esim_internal::parse_tlv(encoded, root, message) ||
        root.tag.size() != 1U || root.tag[0] != 0x30U) {
        message = "ES9+ serverSigned1 DER 对象无效";
        return false;
    }
    static constexpr uint8_t TAG_TRANSACTION[] = {0x80};
    static constexpr uint8_t TAG_CHALLENGE[] = {0x81};
    static constexpr uint8_t TAG_ADDRESS[] = {0x83};
    static constexpr uint8_t TAG_SERVER_CHALLENGE[] = {0x84};
    bool duplicate = false;
    const idf_esim_internal::Tlv* transaction =
        unique_child(root, TAG_TRANSACTION, sizeof(TAG_TRANSACTION), duplicate);
    if (duplicate || !transaction || transaction->value != transaction_id) {
        message = "ES9+ serverSigned1 transactionId 不匹配";
        return false;
    }
    const idf_esim_internal::Tlv* challenge =
        unique_child(root, TAG_CHALLENGE, sizeof(TAG_CHALLENGE), duplicate);
    if (duplicate || !challenge || challenge->value.size() != euicc_challenge.size() ||
        !std::equal(challenge->value.begin(), challenge->value.end(), euicc_challenge.begin())) {
        message = "ES9+ serverSigned1 eUICC challenge 不匹配";
        return false;
    }
    SensitiveText address;
    const idf_esim_internal::Tlv* address_tlv =
        unique_child(root, TAG_ADDRESS, sizeof(TAG_ADDRESS), duplicate);
    if (duplicate || !address_tlv || address_tlv->value.empty()) {
        message = "ES9+ serverSigned1 缺少服务器地址";
        return false;
    }
    address.text.assign(reinterpret_cast<const char*>(address_tlv->value.data()),
                        address_tlv->value.size());
    if (!is_printable_ascii(address.text) ||
        lower_ascii_copy(address.text) != lower_ascii_copy(host)) {
        message = "ES9+ serverSigned1 服务器地址不匹配";
        return false;
    }
    const idf_esim_internal::Tlv* server_challenge =
        unique_child(root, TAG_SERVER_CHALLENGE, sizeof(TAG_SERVER_CHALLENGE), duplicate);
    if (duplicate || !server_challenge || server_challenge->value.size() != 16U) {
        message = "ES9+ serverSigned1 serverChallenge 长度无效";
        return false;
    }
    return true;
}

static bool validate_encoded_object(const std::vector<uint8_t>& encoded,
                                    const uint8_t* tag,
                                    size_t tag_len,
                                    size_t max_size,
                                    const char* name,
                                    std::string& message)
{
    if (encoded.empty() || encoded.size() > max_size) {
        message = name;
        message += "大小无效";
        return false;
    }
    SensitiveTlv object_holder;
    idf_esim_internal::Tlv& object = object_holder.value;
    std::string parse_message;
    if (!idf_esim_internal::parse_tlv(encoded, object, parse_message) ||
        !idf_esim_internal::tag_is(object, tag, tag_len)) {
        message = name;
        message += "DER tag 无效";
        return false;
    }
    return true;
}

static bool encode_imei_tbcd(const std::string& imei,
                             std::array<uint8_t, 8>& encoded,
                             std::string& message)
{
    if (imei.size() != 15U) {
        message = "模组 IMEI 不可用，无法构造 DeviceInfo";
        return false;
    }
    for (unsigned char ch : imei) {
        if (ch < '0' || ch > '9') {
            message = "模组 IMEI 格式无效";
            return false;
        }
    }
    encoded.fill(0);
    for (size_t i = 0; i < 7U; ++i) {
        uint8_t first = static_cast<uint8_t>(imei[i * 2U] - '0');
        uint8_t second = static_cast<uint8_t>(imei[i * 2U + 1U] - '0');
        encoded[i] = static_cast<uint8_t>(first | (second << 4U));
    }
    encoded[7] = static_cast<uint8_t>(0xF0U | static_cast<uint8_t>(imei[14] - '0'));
    return true;
}

static bool build_authenticate_server_request(const LpaActivationCode& activation_code,
                                              const std::vector<uint8_t>& transaction_id,
                                              const std::vector<uint8_t>& server_signed1,
                                              const std::vector<uint8_t>& server_signature1,
                                              const std::vector<uint8_t>& ci_key_id,
                                              const std::vector<uint8_t>& server_certificate,
                                              std::vector<uint8_t>& request,
                                              std::string& message)
{
    SensitiveText imei_text;
    idf_modem_get_imei(imei_text.text);
    std::array<uint8_t, 8> imei = {};
    if (!encode_imei_tbcd(imei_text.text, imei, message)) return false;

    SensitiveBytes device_info_body;
    static constexpr uint8_t TAG_TAC[] = {0x80};
    static constexpr uint8_t TAG_CAPABILITIES[] = {0xA1};
    static constexpr uint8_t TAG_IMEI[] = {0x82};
    SensitiveBytes tac;
    tac.value.assign(imei.begin(), imei.begin() + 4U);
    idf_esim_internal::append_tlv(device_info_body.value, TAG_TAC, tac.value);
    // 首版不虚构无线制式 Release；空 DeviceCapabilities 由 eUICC/SM-DP+按 v2.x 处理。
    idf_esim_internal::append_tlv(device_info_body.value, TAG_CAPABILITIES, {});
    SensitiveBytes imei_value;
    imei_value.value.assign(imei.begin(), imei.end());
    idf_esim_internal::append_tlv(device_info_body.value, TAG_IMEI, imei_value.value);

    SensitiveBytes ctx_body;
    static constexpr uint8_t TAG_MATCHING_ID[] = {0x80};
    static constexpr uint8_t TAG_DEVICE_INFO[] = {0xA1};
    SensitiveBytes matching_id;
    matching_id.value.assign(activation_code.matchingId.begin(), activation_code.matchingId.end());
    idf_esim_internal::append_tlv(ctx_body.value, TAG_MATCHING_ID, matching_id.value);
    idf_esim_internal::append_tlv(ctx_body.value, TAG_DEVICE_INFO, device_info_body.value);

    static constexpr uint8_t TAG_CTX_PARAMS[] = {0xA0};
    SensitiveBytes ctx_params;
    idf_esim_internal::append_tlv(ctx_params.value, TAG_CTX_PARAMS, ctx_body.value);

    SensitiveBytes body;
    body.value.reserve(server_signed1.size() + server_signature1.size() + ci_key_id.size() +
                       server_certificate.size() + ctx_params.value.size());
    body.value.insert(body.value.end(), server_signed1.begin(), server_signed1.end());
    body.value.insert(body.value.end(), server_signature1.begin(), server_signature1.end());
    body.value.insert(body.value.end(), ci_key_id.begin(), ci_key_id.end());
    body.value.insert(body.value.end(), server_certificate.begin(), server_certificate.end());
    body.value.insert(body.value.end(), ctx_params.value.begin(), ctx_params.value.end());

    static constexpr uint8_t TAG_AUTHENTICATE_SERVER[] = {0xBF, 0x38};
    clear_sensitive_bytes(request);
    idf_esim_internal::append_tlv(request, TAG_AUTHENTICATE_SERVER, body.value);
    if (request.size() > 16U * 1024U || transaction_id.empty()) {
        clear_sensitive_bytes(request);
        message = "AuthenticateServer 请求对象大小无效";
        return false;
    }
    return true;
}

static bool parse_success_status(const std::string& json, std::string& message)
{
    SensitiveText status;
    if (!json_get_string(json, "status", status.text, true)) {
        message = "ES9+ 响应缺少 functionExecutionStatus";
        return false;
    }
    if (status.text != "Executed-Success") {
        // 服务器 status 用于定位协议阶段；不回显服务端 message 或原始响应。
        message = "ES9+ 服务器拒绝请求（";
        message += status.text;
        message += "）";
        return false;
    }
    return true;
}

struct LpaAuthSession {
    SensitiveBytes euiccInfo1;
    SensitiveBytes euiccChallenge;
    SensitiveBytes transactionId;
    SensitiveBytes serverSigned1;
    SensitiveBytes serverSignature1;
    SensitiveBytes ciKeyId;
    SensitiveBytes serverCertificate;
    SensitiveBytes authenticateServerRequest;
    SensitiveBytes authenticateServerResponse;
    SensitiveBytes prepareDownloadResponse;
    SensitiveBytes profileMetadata;
    SensitiveBytes smdpSigned2;
    SensitiveBytes smdpSignature2;
    SensitiveBytes smdpCertificate;
    bool confirmationCodeRequired = false;
};

}  // namespace

LpaActivationCode::LpaActivationCode(LpaActivationCode&& other) noexcept
    : smdpHost(std::move(other.smdpHost)),
      matchingId(std::move(other.matchingId)),
      confirmationCodeRequired(other.confirmationCodeRequired),
      extensions(std::move(other.extensions))
{
    other.clear_sensitive();
}

LpaActivationCode& LpaActivationCode::operator=(LpaActivationCode&& other) noexcept
{
    if (this != &other) {
        clear_sensitive();
        smdpHost = std::move(other.smdpHost);
        matchingId = std::move(other.matchingId);
        confirmationCodeRequired = other.confirmationCodeRequired;
        extensions = std::move(other.extensions);
        other.clear_sensitive();
    }
    return *this;
}

void LpaActivationCode::clear_sensitive()
{
    clear_string(smdpHost);
    clear_string(matchingId);
    for (std::string& extension : extensions) clear_string(extension);
    std::vector<std::string>().swap(extensions);
    confirmationCodeRequired = false;
}

LpaActivationCode::~LpaActivationCode()
{
    clear_sensitive();
}

void idf_lpa_clear_sensitive(std::string& value)
{
    clear_string(value);
}

bool idf_lpa_parse_activation_code(const std::string& input,
                                   LpaActivationCode& out,
                                   std::string& message)
{
    out.clear_sensitive();
    message.clear();

    if (input.size() > kMaxInputLength) {
        message = "Activation Code 超过 512 字符";
        return false;
    }
    size_t normalized_begin = 0;
    size_t normalized_end = 0;
    trim_ascii_bounds(input, normalized_begin, normalized_end);
    if (normalized_end == normalized_begin) {
        message = "Activation Code 不能为空";
        return false;
    }
    SensitiveText normalized;
    normalized.assign(input, normalized_begin, normalized_end - normalized_begin);

    bool has_lpa_prefix = normalized.text.rfind("LPA:", 0) == 0;
    if (has_lpa_prefix && normalized.text.compare(kActivationPrefixLength, 1U, "1") != 0) {
        message = "只接受 Activation Code format version 1";
        return false;
    }

    if (has_lpa_prefix && normalized.text.size() < kActivationPrefixLength + 2U) {
        message = "Activation Code 内容为空";
        return false;
    }
    if (!has_lpa_prefix && normalized.text.size() < 3U) {
        message = "Activation Code 内容为空";
        return false;
    }
    const size_t core_offset = has_lpa_prefix ? kActivationPrefixLength : 0U;
    SensitiveText core;
    core.assign(normalized.text, core_offset, normalized.text.size() - core_offset);
    if (core.text.empty()) {
        message = "Activation Code 内容为空";
        return false;
    }
    if (core.text.size() > kMaxActivationCodeLength) {
        message = "Activation Code 超过 512 字符";
        return false;
    }
    if (core.text.find('\0') != std::string::npos || !is_printable_ascii(core.text)) {
        message = "Activation Code 包含非法字符";
        return false;
    }

    SensitiveFields fields;
    fields.values.reserve(kMaxActivationFields);
    if (!split_fields(core.text, fields)) {
        message = "Activation Code 扩展字段过多";
        return false;
    }
    if (fields.values.size() < kMaxCoreFields || fields.values[0] != "1") {
        message = "只接受 Activation Code format version 1，且必须包含主机和 MatchingID 字段";
        return false;
    }
    if (fields.values.size() > kMaxActivationFields) {
        message = "Activation Code 扩展字段过多";
        return false;
    }
    if (!valid_smdp_host(fields.values[1], message)) return false;
    if (!valid_matching_id(fields.values[2], message)) return false;
    for (size_t i = kMaxCoreFields; i < fields.values.size(); ++i) {
        if (fields.values[i].empty() ||
            fields.values[i].size() > kMaxOptionalFieldLength ||
            !is_printable_ascii(fields.values[i])) {
            message = "Activation Code 可选字段为空、过长或包含非法字符";
            return false;
        }
    }

    out.smdpHost = fields.values[1];
    out.matchingId = fields.values[2];
    // Gate 2 不猜测扩展字段语义；真实 CC-required 规则留给 Gate 3 的协议响应。
    out.confirmationCodeRequired = false;
    for (size_t i = kMaxCoreFields; i < fields.values.size() &&
                         out.extensions.size() < kMaxStoredExtensions; ++i) {
        out.extensions.push_back(fields.values[i]);
    }
    return true;
}

std::string idf_lpa_mask_matching_id(const std::string& matching_id)
{
    if (matching_id.empty()) return "（空）";
    if (matching_id.size() <= 4U) return "****";
    const size_t visible = matching_id.size() <= 8U ? 1U : 2U;
    std::string masked;
    masked.reserve(visible * 2U + 4U);
    masked.append(matching_id.data(), visible);
    masked += "****";
    masked.append(matching_id.data() + matching_id.size() - visible, visible);
    return masked;
}

static esp_err_t run_authentication_session(const LpaActivationCode& activation_code,
                                             bool allow_missing_protocol,
                                             LpaAuthenticationResult& result,
                                             LpaAuthSession& session,
                                             std::string& safe_message)
{
    result = LpaAuthenticationResult();
    safe_message.clear();

    SensitiveText host;
    SensitiveText matching_id;
    host.text = activation_code.smdpHost;
    matching_id.text = activation_code.matchingId;
    if (!valid_smdp_host(host.text, safe_message) ||
        !valid_rsp_matching_id(matching_id.text, safe_message)) {
        return ESP_ERR_INVALID_ARG;
    }

    SensitiveBytes& euicc_info1 = session.euiccInfo1;
    SensitiveBytes& server_signed1 = session.serverSigned1;
    SensitiveBytes& server_signature1 = session.serverSignature1;
    SensitiveBytes& ci_key_id = session.ciKeyId;
    SensitiveBytes& server_certificate = session.serverCertificate;
    SensitiveBytes& transaction_id = session.transactionId;
    SensitiveBytes& authenticate_server_request = session.authenticateServerRequest;
    SensitiveBytes& authenticate_server_response = session.authenticateServerResponse;
    SensitiveBytes& profile_metadata = session.profileMetadata;
    SensitiveBytes& smdp_signed2 = session.smdpSigned2;
    SensitiveBytes& smdp_signature2 = session.smdpSignature2;
    SensitiveBytes& smdp_certificate = session.smdpCertificate;
    SensitiveBytes response_transaction_id;
    std::array<uint8_t, 16> euicc_challenge = {};

    esp_err_t err = idf_esim_lpa_get_auth_material(euicc_info1.value,
                                                   euicc_challenge,
                                                   safe_message);
    if (err != ESP_OK) return err;

    session.euiccChallenge.value.assign(euicc_challenge.begin(), euicc_challenge.end());
    SensitiveBytes challenge_bytes;
    challenge_bytes.value.assign(euicc_challenge.begin(), euicc_challenge.end());
    SensitiveText euicc_challenge_b64;
    SensitiveText euicc_info1_b64;
    if (!base64_encode_bytes(challenge_bytes.value, euicc_challenge_b64.text, safe_message) ||
        !base64_encode_bytes(euicc_info1.value, euicc_info1_b64.text, safe_message)) {
        return ESP_FAIL;
    }

    SensitiveText initiate_body;
    initiate_body.text.reserve(euicc_challenge_b64.text.size() + euicc_info1_b64.text.size() +
                               host.text.size() + 128U);
    initiate_body.text.push_back('{');
    bool first = true;
    append_json_field(initiate_body.text, "euiccChallenge", euicc_challenge_b64.text, first);
    append_json_field(initiate_body.text, "euiccInfo1", euicc_info1_b64.text, first);
    append_json_field(initiate_body.text, "smdpAddress", host.text, first);
    initiate_body.text.push_back('}');

    SensitiveText initiate_response;
    err = es9_post_json(host.text,
                        "InitiateAuthentication",
                        allow_missing_protocol,
                        "/gsma/rsp2/es9plus/initiateAuthentication",
                        initiate_body.text,
                        initiate_response.text,
                        safe_message);
    if (err != ESP_OK) return err;
    if (!parse_success_status(initiate_response.text, safe_message)) {
        return ESP_ERR_INVALID_RESPONSE;
    }

    SensitiveText transaction_text;
    SensitiveText server_signed1_b64;
    SensitiveText server_signature1_b64;
    SensitiveText ci_key_id_b64;
    SensitiveText server_certificate_b64;
    if (!json_get_string(initiate_response.text, "transactionId", transaction_text.text, true) ||
        !json_get_string(initiate_response.text, "serverSigned1", server_signed1_b64.text, true) ||
        !json_get_string(initiate_response.text, "serverSignature1", server_signature1_b64.text, true) ||
        !json_get_string(initiate_response.text, "serverCertificate", server_certificate_b64.text, true)) {
        safe_message = "ES9+ InitiateAuthentication 响应字段不完整";
        return ESP_ERR_INVALID_RESPONSE;
    }
    bool has_ci_key = initiate_response.text.find("\"euiccCiPKIdToBeUsed\"") != std::string::npos;
    bool has_ci_key_legacy = initiate_response.text.find("\"euiccCiPKIdTobeUsed\"") != std::string::npos;
    if (has_ci_key == has_ci_key_legacy) {
        safe_message = "ES9+ InitiateAuthentication CI key 字段无效";
        return ESP_ERR_INVALID_RESPONSE;
    }
    const char* ci_key_name = has_ci_key ? "euiccCiPKIdToBeUsed" : "euiccCiPKIdTobeUsed";
    if (!json_get_string(initiate_response.text, ci_key_name, ci_key_id_b64.text, true) ||
        !decode_transaction_id(transaction_text.text, transaction_id.value, safe_message) ||
        !base64_decode_bounded(server_signed1_b64.text, kMaxEs9Object,
                               server_signed1.value, safe_message) ||
        !base64_decode_bounded(server_signature1_b64.text, kMaxEs9Object,
                               server_signature1.value, safe_message) ||
        !base64_decode_bounded(ci_key_id_b64.text, 128U, ci_key_id.value, safe_message) ||
        !base64_decode_bounded(server_certificate_b64.text, kMaxEs9Object,
                               server_certificate.value, safe_message)) {
        return ESP_ERR_INVALID_RESPONSE;
    }

    static constexpr uint8_t TAG_SERVER_SIGNATURE[] = {0x5F, 0x37};
    static constexpr uint8_t TAG_CI_KEY_ID[] = {0x04};
    static constexpr uint8_t TAG_CERTIFICATE[] = {0x30};
    if (!validate_server_signed1(server_signed1.value, transaction_id.value,
                                 euicc_challenge, host.text, safe_message) ||
        !validate_encoded_object(server_signature1.value, TAG_SERVER_SIGNATURE,
                                 sizeof(TAG_SERVER_SIGNATURE), 1024U,
                                 "ES9+ serverSignature1 ", safe_message) ||
        !validate_encoded_object(ci_key_id.value, TAG_CI_KEY_ID, sizeof(TAG_CI_KEY_ID),
                                 128U, "ES9+ euiccCiPKIdToBeUsed ", safe_message) ||
        !validate_encoded_object(server_certificate.value, TAG_CERTIFICATE,
                                 sizeof(TAG_CERTIFICATE), kMaxEs9Object,
                                 "ES9+ serverCertificate ", safe_message)) {
        return ESP_ERR_INVALID_RESPONSE;
    }

    if (!build_authenticate_server_request(activation_code, transaction_id.value,
                                           server_signed1.value, server_signature1.value,
                                           ci_key_id.value, server_certificate.value,
                                           authenticate_server_request.value, safe_message)) {
        return ESP_ERR_INVALID_RESPONSE;
    }
    err = idf_esim_lpa_authenticate_server(authenticate_server_request.value,
                                            authenticate_server_response.value,
                                            safe_message);
    if (err != ESP_OK) return err;

    static constexpr uint8_t TAG_AUTHENTICATE_SERVER_RESPONSE[] = {0xBF, 0x38};
    if (!validate_encoded_object(authenticate_server_response.value,
                                 TAG_AUTHENTICATE_SERVER_RESPONSE,
                                 sizeof(TAG_AUTHENTICATE_SERVER_RESPONSE),
                                 16U * 1024U,
                                 "ES10b AuthenticateServerResponse ", safe_message)) {
        return ESP_ERR_INVALID_RESPONSE;
    }

    SensitiveText authenticate_server_response_b64;
    if (!base64_encode_bytes(authenticate_server_response.value,
                             authenticate_server_response_b64.text, safe_message)) {
        return ESP_FAIL;
    }
    SensitiveText authenticate_client_body;
    authenticate_client_body.text.reserve(transaction_text.text.size() +
                                          authenticate_server_response_b64.text.size() + 96U);
    authenticate_client_body.text.push_back('{');
    first = true;
    SensitiveText transaction_upper;
    transaction_upper.text = transaction_text.text;
    for (char& ch : transaction_upper.text) {
        if (ch >= 'a' && ch <= 'f') ch = static_cast<char>(ch - 'a' + 'A');
    }
    append_json_field(authenticate_client_body.text, "transactionId",
                      transaction_upper.text, first);
    append_json_field(authenticate_client_body.text, "authenticateServerResponse",
                      authenticate_server_response_b64.text, first);
    authenticate_client_body.text.push_back('}');

    SensitiveText authenticate_client_response;
    err = es9_post_json(host.text,
                        "AuthenticateClient",
                        allow_missing_protocol,
                        "/gsma/rsp2/es9plus/authenticateClient",
                        authenticate_client_body.text,
                        authenticate_client_response.text,
                        safe_message);
    if (err != ESP_OK) return err;
    if (!parse_success_status(authenticate_client_response.text, safe_message)) {
        return ESP_ERR_INVALID_RESPONSE;
    }
    SensitiveText response_transaction_text;
    if (!json_get_string(authenticate_client_response.text, "transactionId",
                         response_transaction_text.text, true) ||
        !decode_transaction_id(response_transaction_text.text,
                               response_transaction_id.value, safe_message) ||
        response_transaction_id.value != transaction_id.value) {
        safe_message = "ES9+ AuthenticateClient transactionId 不匹配";
        return ESP_ERR_INVALID_RESPONSE;
    }

    SensitiveText profile_metadata_b64;
    SensitiveText smdp_signed2_b64;
    SensitiveText smdp_signature2_b64;
    SensitiveText smdp_certificate_b64;
    if (!json_get_string(authenticate_client_response.text, "profileMetadata",
                         profile_metadata_b64.text, true) ||
        !json_get_string(authenticate_client_response.text, "smdpSigned2",
                         smdp_signed2_b64.text, true) ||
        !json_get_string(authenticate_client_response.text, "smdpSignature2",
                         smdp_signature2_b64.text, true) ||
        !json_get_string(authenticate_client_response.text, "smdpCertificate",
                         smdp_certificate_b64.text, true) ||
        !base64_decode_bounded(profile_metadata_b64.text, kMaxEs9Object,
                               profile_metadata.value, safe_message) ||
        !base64_decode_bounded(smdp_signed2_b64.text, kMaxEs9Object,
                               smdp_signed2.value, safe_message) ||
        !base64_decode_bounded(smdp_signature2_b64.text, kMaxEs9Object,
                               smdp_signature2.value, safe_message) ||
        !base64_decode_bounded(smdp_certificate_b64.text, kMaxEs9Object,
                               smdp_certificate.value, safe_message)) {
        return ESP_ERR_INVALID_RESPONSE;
    }
    if (profile_metadata.value.empty()) {
        safe_message = "ES9+ AuthenticateClient profileMetadata 为空";
        return ESP_ERR_INVALID_RESPONSE;
    }
    if (!validate_encoded_object(smdp_signed2.value, TAG_CERTIFICATE,
                                 sizeof(TAG_CERTIFICATE), kMaxEs9Object,
                                 "ES9+ smdpSigned2 ", safe_message) ||
        !validate_encoded_object(smdp_signature2.value, TAG_SERVER_SIGNATURE,
                                 sizeof(TAG_SERVER_SIGNATURE), 1024U,
                                 "ES9+ smdpSignature2 ", safe_message) ||
        !validate_encoded_object(smdp_certificate.value, TAG_CERTIFICATE,
                                 sizeof(TAG_CERTIFICATE), kMaxEs9Object,
                                 "ES9+ smdpCertificate ", safe_message)) {
        return ESP_ERR_INVALID_RESPONSE;
    }

    SensitiveTlv signed2_holder;
    idf_esim_internal::Tlv& signed2 = signed2_holder.value;
    std::string signed2_message;
    if (!idf_esim_internal::parse_tlv(smdp_signed2.value, signed2, signed2_message)) {
        safe_message = "ES9+ smdpSigned2 DER 对象无效";
        return ESP_ERR_INVALID_RESPONSE;
    }
    static constexpr uint8_t TAG_SIGNED2_TRANSACTION[] = {0x80};
    static constexpr uint8_t TAG_CC_REQUIRED[] = {0x01};
    bool duplicate_transaction = false;
    bool duplicate_cc_required = false;
    const idf_esim_internal::Tlv* signed2_transaction =
        unique_child(signed2, TAG_SIGNED2_TRANSACTION,
                     sizeof(TAG_SIGNED2_TRANSACTION), duplicate_transaction);
    const idf_esim_internal::Tlv* cc_required =
        unique_child(signed2, TAG_CC_REQUIRED, sizeof(TAG_CC_REQUIRED), duplicate_cc_required);
    if (duplicate_transaction || duplicate_cc_required || !signed2_transaction ||
        signed2_transaction->value != transaction_id.value ||
        !cc_required || cc_required->value.size() != 1U) {
        safe_message = "ES9+ smdpSigned2 transactionId 或 Confirmation Code 标记无效";
        return ESP_ERR_INVALID_RESPONSE;
    }
    result.confirmationCodeRequired = cc_required->value[0] != 0U;
    session.confirmationCodeRequired = result.confirmationCodeRequired;
    safe_message = result.confirmationCodeRequired
        ? "ES9+ 认证完成，服务器要求 Confirmation Code"
        : "ES9+ 认证完成，尚未写入 Profile";
    return ESP_OK;
}

esp_err_t idf_lpa_run_authentication(const LpaActivationCode& activation_code,
                                     LpaAuthenticationResult& result,
                                     std::string& safe_message)
{
    LpaAuthSession session;
    return run_authentication_session(activation_code, false, result, session, safe_message);
}

namespace {

static constexpr size_t kMaxBppEncodedBytes = 1536U * 1024U;
static constexpr size_t kMaxBppDecodedBytes = 1024U * 1024U;
static constexpr size_t kMaxBppSegmentBytes = kMaxBppDecodedBytes;
static constexpr size_t kMaxBppElements = 4096U;

static void download_phase(const LpaDownloadObserver& observer,
                           const char* phase,
                           const char* message)
{
    if (observer.set_phase) observer.set_phase(observer.context, phase, message);
}

static void sample_heap(LpaDownloadStats& stats)
{
    const size_t free_heap = heap_caps_get_free_size(MALLOC_CAP_8BIT);
    const size_t minimum = heap_caps_get_minimum_free_size(MALLOC_CAP_8BIT);
    const size_t largest = heap_caps_get_largest_free_block(MALLOC_CAP_8BIT);
    if (free_heap > stats.peakFreeHeap) stats.peakFreeHeap = free_heap;
    if (stats.minimumFreeHeap == 0 || minimum < stats.minimumFreeHeap) {
        stats.minimumFreeHeap = minimum;
    }
    if (largest > stats.largestFreeBlock) stats.largestFreeBlock = largest;
}

class BppSegmentWriter {
public:
    ~BppSegmentWriter() { close(); }

    esp_err_t begin(std::string& message)
    {
        close();
        pending_size_ = 0;
        block_number_ = 0;
        clear_sensitive_bytes(last_response_);
        active_ = true;
        esp_err_t err = session_.begin_segment(message);
        if (err != ESP_OK) active_ = false;
        return err;
    }

    esp_err_t write(const uint8_t* data, size_t length, std::string& message)
    {
        if (!active_) {
            message = "BPP segment writer 未打开";
            return ESP_ERR_INVALID_STATE;
        }
        if (!data && length != 0) {
            message = "BPP segment 数据无效";
            return ESP_ERR_INVALID_ARG;
        }
        if (length > kMaxBppSegmentBytes || segment_bytes_ > kMaxBppSegmentBytes - length) {
            message = "BPP segment 超过大小上限";
            return ESP_ERR_INVALID_SIZE;
        }
        segment_bytes_ += length;
        while (length > 0) {
            if (pending_size_ == pending_.size()) {
                esp_err_t err = flush(false, message);
                if (err != ESP_OK) return err;
            }
            const size_t n = std::min(length, pending_.size() - pending_size_);
            memcpy(pending_.data() + pending_size_, data, n);
            pending_size_ += n;
            data += n;
            length -= n;
        }
        return ESP_OK;
    }

    esp_err_t finish(std::vector<uint8_t>& response, std::string& message)
    {
        clear_sensitive_bytes(response);
        if (!active_ || segment_bytes_ == 0 || pending_size_ == 0) {
            message = "BPP segment 为空或未完成";
            close();
            return ESP_ERR_INVALID_STATE;
        }
        esp_err_t err = flush(true, message);
        if (err == ESP_OK) response = std::move(last_response_);
        close();
        return err;
    }

    void close()
    {
        session_.close();
        active_ = false;
        volatile uint8_t* pending_bytes = pending_.data();
        for (size_t i = 0; i < pending_.size(); ++i) pending_bytes[i] = 0;
        pending_size_ = 0;
        segment_bytes_ = 0;
        block_number_ = 0;
        clear_sensitive_bytes(last_response_);
    }

private:
    esp_err_t flush(bool last, std::string& message)
    {
        if (pending_size_ == 0 || block_number_ > 0xFFU) {
            message = "BPP segment transport block 超过上限";
            return ESP_ERR_INVALID_SIZE;
        }
        SensitiveBytes response;
        esp_err_t err = session_.write_block(pending_.data(), pending_size_, last,
                                             static_cast<uint8_t>(block_number_),
                                             response.value, message);
        if (err != ESP_OK) return err;
        if (!last && !response.value.empty()) {
            message = "BPP 中间 block 返回了异常响应数据";
            return ESP_ERR_INVALID_RESPONSE;
        }
        if (last) {
            clear_sensitive_bytes(last_response_);
            last_response_ = std::move(response.value);
        }
        pending_size_ = 0;
        ++block_number_;
        return ESP_OK;
    }

    IdfEsimLpaBppSession session_;
    std::array<uint8_t, 120> pending_ = {};
    size_t pending_size_ = 0;
    size_t segment_bytes_ = 0;
    uint16_t block_number_ = 0;
    bool active_ = false;
    std::vector<uint8_t> last_response_;
};

class DerHeaderReader {
public:
    void reset()
    {
        raw_.clear();
        tag_bytes_ = 0;
        length_bytes_ = 0;
        length_ = 0;
        complete_ = false;
    }

    bool consume(uint8_t byte, std::string& message)
    {
        if (complete_) {
            message = "DER header 已完成";
            return false;
        }
        if (raw_.empty()) {
            raw_.push_back(byte);
            if (byte == 0xBFU) {
                tag_bytes_ = 2;
            } else if ((byte & 0x1FU) == 0x1FU) {
                message = "BPP 不支持高位 tag 编码";
                return false;
            } else {
                tag_bytes_ = 1;
            }
            return true;
        }
        if (raw_.size() < tag_bytes_) {
            raw_.push_back(byte);
            return true;
        }
        if (raw_.size() == tag_bytes_) {
            raw_.push_back(byte);
            if (byte < 0x80U) {
                length_ = byte;
                complete_ = true;
                return true;
            }
            if (byte >= 0x81U && byte <= 0x84U) {
                length_bytes_ = byte & 0x7FU;
            } else {
                message = "BPP DER length 编码无效";
                return false;
            }
            return true;
        }
        raw_.push_back(byte);
        if (raw_.size() - tag_bytes_ - 1U == length_bytes_) {
            uint64_t parsed_length = 0;
            for (size_t i = 0; i < length_bytes_; ++i) {
                parsed_length = (parsed_length << 8U) |
                                 static_cast<uint64_t>(raw_[tag_bytes_ + 1U + i]);
            }
            if (parsed_length > static_cast<uint64_t>(std::numeric_limits<size_t>::max())) {
                message = "BPP DER length 超出范围";
                return false;
            }
            length_ = static_cast<size_t>(parsed_length);
            if (length_ < 0x80U) {
                message = "BPP DER 长格式使用了非最短编码";
                return false;
            }
            complete_ = true;
        }
        return true;
    }

    bool complete() const { return complete_; }
    size_t length() const { return length_; }
    const std::vector<uint8_t>& raw() const { return raw_; }
    bool tag_is(uint8_t first, uint8_t second = 0) const
    {
        return raw_.size() >= 2U && raw_[0] == first && raw_[1] == second &&
               ((first == 0xBFU) ? raw_.size() >= 2U : raw_.size() >= 1U);
    }
    bool one_byte_tag(uint8_t tag) const
    {
        return raw_.size() >= 1U && raw_[0] == tag && tag_bytes_ == 1U;
    }

private:
    std::vector<uint8_t> raw_;
    size_t tag_bytes_ = 0;
    size_t length_bytes_ = 0;
    size_t length_ = 0;
    bool complete_ = false;
};

class BppStreamParser {
public:
    BppStreamParser() = default;

    esp_err_t feed(const uint8_t* data, size_t length, std::string& message);
    esp_err_t finish(std::string& message);
    const std::vector<uint8_t>& installation_result() const { return installation_result_.value; }
    size_t decoded_bytes() const { return decoded_bytes_; }
    size_t input_bytes() const { return input_bytes_; }
    size_t segment_count() const { return segment_count_; }
    size_t failure_offset() const { return failure_offset_; }
    const char* failure_state() const { return failure_state_; }
    const std::vector<uint8_t>& failure_header() const { return failure_header_; }

private:
    enum class State {
        outer_header,
        outer_child,
        first_sequence_header,
        first_sequence_child,
        metadata_sequence_header,
        metadata_child,
        second_sequence_or_profile,
        second_sequence_child,
        profile_sequence_header,
        profile_child,
        value,
        done,
        failed,
    };

    enum class ValueKind {
        outer_child,
        first_sequence_child,
        metadata_child,
        second_sequence_child,
        profile_child,
    };

    esp_err_t handle_header(std::string& message);
    esp_err_t consume_value_byte(uint8_t byte, std::string& message);
    esp_err_t emit(const uint8_t* data, size_t length, std::string& message);
    esp_err_t finish_segment(std::string& message);
    bool expect_tag(bool two_byte, uint8_t first, uint8_t second = 0) const;
    static const char* state_name(State state);
    void record_failure();
    esp_err_t fail_preserving_message(std::string& message, const char* fallback);
    esp_err_t fail(const char* text, std::string& message);

    State state_ = State::outer_header;
    ValueKind value_kind_ = ValueKind::outer_child;
    DerHeaderReader header_;
    BppSegmentWriter writer_;
    size_t value_remaining_ = 0;
    size_t outer_remaining_ = 0;
    size_t sequence_remaining_ = 0;
    size_t child_count_ = 0;
    size_t decoded_bytes_ = 0;
    size_t input_bytes_ = 0;
    size_t segment_count_ = 0;
    size_t failure_offset_ = 0;
    const char* failure_state_ = "none";
    std::vector<uint8_t> failure_header_;
    SensitiveBytes installation_result_;
    bool sequence_active_ = false;
    bool failure_recorded_ = false;
};

bool BppStreamParser::expect_tag(bool two_byte, uint8_t first, uint8_t second) const
{
    return two_byte ? header_.tag_is(first, second) : header_.one_byte_tag(first);
}

const char* BppStreamParser::state_name(State state)
{
    switch (state) {
        case State::outer_header: return "outer_header";
        case State::outer_child: return "outer_child";
        case State::first_sequence_header: return "first_sequence_header";
        case State::first_sequence_child: return "first_sequence_child";
        case State::metadata_sequence_header: return "metadata_sequence_header";
        case State::metadata_child: return "metadata_child";
        case State::second_sequence_or_profile: return "second_sequence_or_profile";
        case State::second_sequence_child: return "second_sequence_child";
        case State::profile_sequence_header: return "profile_sequence_header";
        case State::profile_child: return "profile_child";
        case State::value: return "value";
        case State::done: return "done";
        case State::failed: return "failed";
    }
    return "unknown";
}

void BppStreamParser::record_failure()
{
    if (failure_recorded_) return;
    failure_recorded_ = true;
    failure_offset_ = input_bytes_ == 0 ? 0 : input_bytes_ - 1U;
    failure_state_ = state_name(state_);
    failure_header_ = header_.raw();
}

esp_err_t BppStreamParser::fail_preserving_message(std::string& message, const char* fallback)
{
    record_failure();
    state_ = State::failed;
    writer_.close();
    if (message.empty()) message = fallback ? fallback : "BPP 结构无效";
    return ESP_ERR_INVALID_RESPONSE;
}

esp_err_t BppStreamParser::fail(const char* text, std::string& message)
{
    record_failure();
    state_ = State::failed;
    writer_.close();
    message = text ? text : "BPP 结构无效";
    return ESP_ERR_INVALID_RESPONSE;
}

esp_err_t BppStreamParser::emit(const uint8_t* data, size_t length, std::string& message)
{
    if (length == 0) return ESP_OK;
    if (outer_remaining_ < length || (sequence_active_ && sequence_remaining_ < length)) {
        return fail("BPP DER 容器长度不匹配", message);
    }
    esp_err_t err = writer_.write(data, length, message);
    if (err != ESP_OK) return err;
    outer_remaining_ -= length;
    if (sequence_active_) sequence_remaining_ -= length;
    if (decoded_bytes_ > kMaxBppDecodedBytes - length) {
        return fail("BPP decoded 数据超过大小上限", message);
    }
    decoded_bytes_ += length;
    return ESP_OK;
}

esp_err_t BppStreamParser::finish_segment(std::string& message)
{
    std::vector<uint8_t> response;
    esp_err_t err = writer_.finish(response, message);
    if (err != ESP_OK) return err;
    if (!response.empty()) {
        if (!installation_result_.value.empty()) {
            return fail("BPP 返回了多个 ProfileInstallationResult", message);
        }
        installation_result_.value = std::move(response);
    }
    ++segment_count_;
    if (segment_count_ > kMaxBppElements) return fail("BPP segment 数量超过上限", message);
    return ESP_OK;
}

esp_err_t BppStreamParser::handle_header(std::string& message)
{
    const std::vector<uint8_t> raw = header_.raw();
    const size_t length = header_.length();
    const bool large_sequence_header = state_ == State::metadata_sequence_header ||
                                       state_ == State::profile_sequence_header;
    if (raw.empty() ||
        (state_ == State::outer_header && length > kMaxBppDecodedBytes) ||
        (state_ != State::outer_header && !large_sequence_header &&
         length > kMaxBppSegmentBytes) ||
        (large_sequence_header && length > kMaxBppDecodedBytes)) {
        return fail("BPP DER header 大小无效", message);
    }

    switch (state_) {
        case State::outer_header: {
            if (!expect_tag(true, 0xBF, 0x36) || length == 0) {
                return fail("BPP 外层 tag 无效", message);
            }
            outer_remaining_ = length;
            esp_err_t err = writer_.begin(message);
            if (err != ESP_OK) return err;
            err = writer_.write(raw.data(), raw.size(), message);
            if (err != ESP_OK) return err;
            decoded_bytes_ += raw.size();
            state_ = State::outer_child;
            return ESP_OK;
        }
        case State::outer_child: {
            if (!expect_tag(true, 0xBF, 0x23) || length == 0) {
                return fail("BPP InitialiseSecureChannel tag 无效", message);
            }
            esp_err_t err = emit(raw.data(), raw.size(), message);
            if (err != ESP_OK) return err;
            value_remaining_ = length;
            value_kind_ = ValueKind::outer_child;
            state_ = State::value;
            return ESP_OK;
        }
        case State::first_sequence_header: {
            if (!expect_tag(false, 0xA0) || length == 0) {
                return fail("BPP firstSequenceOf87 tag 无效", message);
            }
            esp_err_t err = writer_.begin(message);
            if (err != ESP_OK) return err;
            err = emit(raw.data(), raw.size(), message);
            if (err != ESP_OK) return err;
            sequence_remaining_ = length;
            sequence_active_ = true;
            child_count_ = 0;
            state_ = State::first_sequence_child;
            return ESP_OK;
        }
        case State::first_sequence_child: {
            if (!expect_tag(false, 0x87) || length == 0) {
                return fail("BPP first 87 TLV 无效", message);
            }
            esp_err_t err = emit(raw.data(), raw.size(), message);
            if (err != ESP_OK) return err;
            value_remaining_ = length;
            value_kind_ = ValueKind::first_sequence_child;
            state_ = State::value;
            return ESP_OK;
        }
        case State::metadata_sequence_header: {
            if (!expect_tag(false, 0xA1) || length == 0) {
                return fail("BPP sequenceOf88 tag 无效", message);
            }
            esp_err_t err = writer_.begin(message);
            if (err != ESP_OK) return err;
            err = emit(raw.data(), raw.size(), message);
            if (err != ESP_OK) return err;
            sequence_remaining_ = length;
            sequence_active_ = true;
            child_count_ = 0;
            err = finish_segment(message);
            if (err != ESP_OK) return err;
            state_ = State::metadata_child;
            return ESP_OK;
        }
        case State::metadata_child: {
            if (!expect_tag(false, 0x88) || length == 0) {
                return fail("BPP 88 TLV 无效", message);
            }
            esp_err_t err = writer_.begin(message);
            if (err != ESP_OK) return err;
            err = emit(raw.data(), raw.size(), message);
            if (err != ESP_OK) return err;
            value_remaining_ = length;
            value_kind_ = ValueKind::metadata_child;
            state_ = State::value;
            return ESP_OK;
        }
        case State::second_sequence_or_profile: {
            if (expect_tag(false, 0xA2)) {
                if (length == 0) return fail("BPP secondSequenceOf87 为空", message);
                esp_err_t err = writer_.begin(message);
                if (err != ESP_OK) return err;
                err = emit(raw.data(), raw.size(), message);
                if (err != ESP_OK) return err;
                sequence_remaining_ = length;
                sequence_active_ = true;
                child_count_ = 0;
                state_ = State::second_sequence_child;
                return ESP_OK;
            }
            if (!expect_tag(false, 0xA3) || length == 0) {
                return fail("BPP sequenceOf86 tag 无效", message);
            }
            esp_err_t err = writer_.begin(message);
            if (err != ESP_OK) return err;
            err = emit(raw.data(), raw.size(), message);
            if (err != ESP_OK) return err;
            sequence_remaining_ = length;
            sequence_active_ = true;
            child_count_ = 0;
            err = finish_segment(message);
            if (err != ESP_OK) return err;
            state_ = State::profile_child;
            return ESP_OK;
        }
        case State::second_sequence_child: {
            if (!expect_tag(false, 0x87) || length == 0) {
                return fail("BPP second 87 TLV 无效", message);
            }
            esp_err_t err = emit(raw.data(), raw.size(), message);
            if (err != ESP_OK) return err;
            value_remaining_ = length;
            value_kind_ = ValueKind::second_sequence_child;
            state_ = State::value;
            return ESP_OK;
        }
        case State::profile_sequence_header: {
            if (!expect_tag(false, 0xA3) || length == 0) {
                return fail("BPP sequenceOf86 tag 无效", message);
            }
            esp_err_t err = writer_.begin(message);
            if (err != ESP_OK) return err;
            err = emit(raw.data(), raw.size(), message);
            if (err != ESP_OK) return err;
            sequence_remaining_ = length;
            sequence_active_ = true;
            child_count_ = 0;
            err = finish_segment(message);
            if (err != ESP_OK) return err;
            state_ = State::profile_child;
            return ESP_OK;
        }
        case State::profile_child: {
            if (!expect_tag(false, 0x86) || length == 0) {
                return fail("BPP 86 TLV 无效", message);
            }
            esp_err_t err = writer_.begin(message);
            if (err != ESP_OK) return err;
            err = emit(raw.data(), raw.size(), message);
            if (err != ESP_OK) return err;
            value_remaining_ = length;
            value_kind_ = ValueKind::profile_child;
            state_ = State::value;
            return ESP_OK;
        }
        case State::value:
        case State::done:
        case State::failed:
            return fail("BPP DER 状态无效", message);
    }
    return fail("BPP 状态无效", message);
}

esp_err_t BppStreamParser::consume_value_byte(uint8_t byte, std::string& message)
{
    esp_err_t err = emit(&byte, 1U, message);
    if (err != ESP_OK) return err;
    if (value_remaining_ == 0) return fail("BPP value 长度下溢", message);
    --value_remaining_;
    if (value_remaining_ != 0) return ESP_OK;

    switch (value_kind_) {
        case ValueKind::outer_child:
            err = finish_segment(message);
            if (err != ESP_OK) return err;
            state_ = State::first_sequence_header;
            break;
        case ValueKind::first_sequence_child:
            if (sequence_remaining_ != 0) return fail("BPP firstSequenceOf87 长度错误", message);
            sequence_active_ = false;
            err = finish_segment(message);
            if (err != ESP_OK) return err;
            state_ = State::metadata_sequence_header;
            break;
        case ValueKind::metadata_child:
            err = finish_segment(message);
            if (err != ESP_OK) return err;
            ++child_count_;
            state_ = State::metadata_child;
            break;
        case ValueKind::second_sequence_child:
            if (sequence_remaining_ != 0) return fail("BPP secondSequenceOf87 长度错误", message);
            sequence_active_ = false;
            err = finish_segment(message);
            if (err != ESP_OK) return err;
            state_ = State::profile_sequence_header;
            break;
        case ValueKind::profile_child:
            err = finish_segment(message);
            if (err != ESP_OK) return err;
            ++child_count_;
            state_ = State::profile_child;
            break;
    }
    return ESP_OK;
}

esp_err_t BppStreamParser::feed(const uint8_t* data, size_t length, std::string& message)
{
    if (!data && length != 0) return fail("BPP 输入为空", message);
    if (state_ == State::failed || state_ == State::done) {
        return fail("BPP 在终态后仍收到数据", message);
    }
    for (size_t i = 0; i < length; ++i) {
        ++input_bytes_;
        if (state_ == State::metadata_child && sequence_remaining_ == 0) {
            if (child_count_ == 0) return fail("BPP sequenceOf88 为空", message);
            sequence_active_ = false;
            state_ = State::second_sequence_or_profile;
            // 当前字节就是 A2/A3 的首字节，状态切换后必须继续解析它，不能丢弃。
        }
        if (state_ == State::profile_child && sequence_remaining_ == 0) {
            if (child_count_ == 0 || outer_remaining_ != 0) {
                return fail("BPP sequenceOf86 或外层长度错误", message);
            }
            sequence_active_ = false;
            state_ = State::done;
            return fail("BPP 在输入结束前出现尾随数据", message);
        }
        if (state_ == State::done) return fail("BPP 存在尾随数据", message);
        if (state_ == State::value) {
            esp_err_t err = consume_value_byte(data[i], message);
            if (err != ESP_OK) return err;
            continue;
        }
        if (!header_.consume(data[i], message)) {
            return fail_preserving_message(message, "BPP DER header 无效");
        }
        if (!header_.complete()) continue;
        esp_err_t err = handle_header(message);
        header_.reset();
        if (err != ESP_OK) return err;
    }
    return ESP_OK;
}

esp_err_t BppStreamParser::finish(std::string& message)
{
    if (state_ == State::metadata_child && sequence_remaining_ == 0) {
        if (child_count_ == 0) return fail("BPP sequenceOf88 为空", message);
        sequence_active_ = false;
        state_ = State::second_sequence_or_profile;
    }
    if (state_ == State::profile_child && sequence_remaining_ == 0) {
        if (child_count_ == 0 || outer_remaining_ != 0) {
            return fail("BPP sequenceOf86 或外层长度错误", message);
        }
        sequence_active_ = false;
        state_ = State::done;
    }
    if (state_ != State::done || !header_.raw().empty() || outer_remaining_ != 0) {
        return fail("BPP JSON/Base64 结束时 DER 对象不完整", message);
    }
    return ESP_OK;
}

class BppBase64Decoder {
public:
    explicit BppBase64Decoder(BppStreamParser& parser) : parser_(parser) {}

    esp_err_t feed(char ch, std::string& message)
    {
        if (ch == '\r' || ch == '\n' || ch == ' ' || ch == '\t') {
            return fail("BPP Base64 不接受空白字符", message);
        }
        if (finished_) return fail("BPP Base64 padding 后仍有数据", message);
        if (encoded_chars_ >= kMaxBppEncodedBytes) {
            return fail("BPP Base64 超过大小上限", message);
        }
        const int value = base64_value(ch);
        if (value == -2) {
            if (quartet_size_ < 2) return fail("BPP Base64 padding 位置无效", message);
            quartet_[quartet_size_++] = 0;
            padding_count_++;
            if (padding_count_ > 2) return fail("BPP Base64 padding 无效", message);
        } else if (value >= 0) {
            if (padding_count_ != 0) return fail("BPP Base64 padding 后仍有数据", message);
            quartet_[quartet_size_++] = static_cast<uint8_t>(value);
        } else {
            return fail("BPP Base64 字符无效", message);
        }
        ++encoded_chars_;
        if (quartet_size_ == 4) {
            uint8_t bytes[3] = {
                static_cast<uint8_t>((quartet_[0] << 2U) | (quartet_[1] >> 4U)),
                static_cast<uint8_t>((quartet_[1] << 4U) | (quartet_[2] >> 2U)),
                static_cast<uint8_t>((quartet_[2] << 6U) | quartet_[3]),
            };
            const size_t output = padding_count_ == 2 ? 1U : (padding_count_ == 1 ? 2U : 3U);
            if (padding_count_ == 2 && quartet_[2] != 0) {
                return fail("BPP Base64 非规范 padding", message);
            }
            if (padding_count_ != 0 && quartet_[3] != 0) {
                return fail("BPP Base64 非规范 padding", message);
            }
            esp_err_t err = parser_.feed(bytes, output, message);
            if (err != ESP_OK) return err;
            if (padding_count_ != 0) finished_ = true;
            quartet_size_ = 0;
            padding_count_ = 0;
        }
        return ESP_OK;
    }

    esp_err_t finish(std::string& message)
    {
        if (quartet_size_ != 0 || encoded_chars_ == 0) {
            return fail("BPP Base64 长度不完整", message);
        }
        return ESP_OK;
    }

    size_t encoded_chars() const { return encoded_chars_; }

private:
    static int base64_value(char ch)
    {
        if (ch >= 'A' && ch <= 'Z') return ch - 'A';
        if (ch >= 'a' && ch <= 'z') return ch - 'a' + 26;
        if (ch >= '0' && ch <= '9') return ch - '0' + 52;
        if (ch == '+') return 62;
        if (ch == '/') return 63;
        if (ch == '=') return -2;
        return -1;
    }

    esp_err_t fail(const char* text, std::string& message)
    {
        message = text;
        return ESP_ERR_INVALID_RESPONSE;
    }

    BppStreamParser& parser_;
    std::array<uint8_t, 4> quartet_ = {};
    size_t quartet_size_ = 0;
    size_t padding_count_ = 0;
    size_t encoded_chars_ = 0;
    bool finished_ = false;
};

class BppJsonStreamScanner {
public:
    BppJsonStreamScanner(BppStreamParser& parser, std::string& message)
        : parser_(parser), decoder_(parser), message_(message) {}

    esp_err_t feed(const char* data, size_t length)
    {
        if (!data && length != 0) return fail("ES9+ BPP 响应为空");
        if (response_bytes_ > kMaxBppEncodedBytes + 64U * 1024U ||
            length > kMaxBppEncodedBytes + 64U * 1024U - response_bytes_) {
            return fail("ES9+ BPP 响应超过大小上限");
        }
        response_bytes_ += length;
        for (size_t i = 0; i < length; ++i) {
            esp_err_t err = consume(data[i]);
            if (err != ESP_OK) return err;
        }
        return ESP_OK;
    }

    esp_err_t finish()
    {
        if (in_string_ || awaiting_value_) return fail("ES9+ BPP JSON 字段不完整");
        if (!status_seen_) return fail("ES9+ BPP 响应缺少 status");
        // 服务器拒绝时按规范可以不返回 boundProfilePackage；先让调用方
        // 根据 status 生成业务错误，不能把它误判成 Base64/DER 错误。
        if (status_ != "Executed-Success") return ESP_OK;
        if (!bpp_seen_) return fail("ES9+ BPP 响应缺少 boundProfilePackage");
        esp_err_t err = decoder_.finish(message_);
        if (err != ESP_OK) {
            failure_stage_ = "base64";
            return err;
        }
        err = parser_.finish(message_);
        if (err != ESP_OK) failure_stage_ = "der";
        return err;
    }

    const std::string& status() const { return status_; }
    const std::string& transaction_id() const { return transaction_id_.text; }
    size_t encoded_bpp_chars() const { return decoder_.encoded_chars(); }
    size_t decoded_bpp_bytes() const { return parser_.decoded_bytes(); }
    size_t segment_count() const { return parser_.segment_count(); }
    size_t parser_failure_offset() const { return parser_.failure_offset(); }
    const char* parser_failure_state() const { return parser_.failure_state(); }
    const char* failure_stage() const { return failure_stage_; }
    const std::vector<uint8_t>& parser_failure_header() const { return parser_.failure_header(); }
    bool status_seen() const { return status_seen_; }
    bool bpp_seen() const { return bpp_seen_; }

private:
    enum class StringRole { none, token, value };

    esp_err_t fail(const char* text)
    {
        failure_stage_ = "json";
        message_ = text;
        return ESP_ERR_INVALID_RESPONSE;
    }

    esp_err_t consume(char ch)
    {
        if (in_string_) {
            if (escape_) {
                escape_ = false;
                if (role_ == StringRole::value && current_key_ == "boundProfilePackage") {
                    return fail("ES9+ BPP Base64 不允许 JSON escape");
                }
                if (role_ == StringRole::value &&
                    (current_key_ == "status" || current_key_ == "transactionId")) {
                    if (!append_small(static_cast<char>(ch))) return fail("ES9+ BPP 字段过长");
                }
                return ESP_OK;
            }
            if (ch == '\\') {
                escape_ = true;
                return ESP_OK;
            }
            if (ch == '"') {
                in_string_ = false;
                if (role_ == StringRole::token) {
                    pending_token_ = token_;
                } else if (role_ == StringRole::value) {
                    esp_err_t err = finish_value();
                    if (err != ESP_OK) return err;
                }
                token_.clear();
                role_ = StringRole::none;
                return ESP_OK;
            }
            if (role_ == StringRole::token) {
                if (token_.size() >= 128U) return fail("ES9+ JSON key 过长");
                token_.push_back(ch);
            } else if (role_ == StringRole::value) {
                if (current_key_ == "boundProfilePackage") {
                    const size_t decoded_before = parser_.input_bytes();
                    esp_err_t err = decoder_.feed(ch, message_);
                    if (err != ESP_OK) {
                        failure_stage_ = parser_.input_bytes() != decoded_before ? "der" : "base64";
                        return err;
                    }
                } else if (current_key_ == "status" || current_key_ == "transactionId") {
                    if (!append_small(ch)) return fail("ES9+ BPP 字段过长");
                }
            }
            return ESP_OK;
        }

        if (awaiting_value_) {
            if (isspace(static_cast<unsigned char>(ch))) return ESP_OK;
            awaiting_value_ = false;
            if (ch == '"') {
                in_string_ = true;
                role_ = StringRole::value;
                escape_ = false;
                value_.clear();
                return ESP_OK;
            }
            current_key_.clear();
            return ESP_OK;
        }
        if (!pending_token_.empty()) {
            if (isspace(static_cast<unsigned char>(ch))) return ESP_OK;
            if (ch == ':') {
                current_key_ = pending_token_;
                pending_token_.clear();
                awaiting_value_ = true;
                return ESP_OK;
            }
            pending_token_.clear();
        }
        if (ch == '"') {
            in_string_ = true;
            role_ = StringRole::token;
            escape_ = false;
            token_.clear();
        }
        return ESP_OK;
    }

    bool append_small(char ch)
    {
        if (value_.size() >= 128U) return false;
        value_.push_back(ch);
        return true;
    }

    esp_err_t finish_value()
    {
        if (current_key_ == "status") {
            if (status_seen_) return fail("ES9+ BPP functionExecutionStatus 重复");
            status_ = value_;
            status_seen_ = true;
        } else if (current_key_ == "transactionId") {
            clear_string(transaction_id_.text);
            transaction_id_.text = value_;
        } else if (current_key_ == "boundProfilePackage") {
            esp_err_t err = decoder_.finish(message_);
            if (err != ESP_OK) {
                failure_stage_ = "base64";
                return err;
            }
            bpp_seen_ = true;
        }
        current_key_.clear();
        clear_string(value_);
        return ESP_OK;
    }

    BppStreamParser& parser_;
    BppBase64Decoder decoder_;
    std::string& message_;
    std::string token_;
    std::string pending_token_;
    std::string current_key_;
    std::string value_;
    std::string status_;
    SensitiveText transaction_id_;
    const char* failure_stage_ = "none";
    size_t response_bytes_ = 0;
    bool in_string_ = false;
    bool escape_ = false;
    bool awaiting_value_ = false;
    bool status_seen_ = false;
    bool bpp_seen_ = false;
    StringRole role_ = StringRole::none;
};

struct Es9BppCapture {
    BppJsonStreamScanner* scanner = nullptr;
    std::string* scannerMessage = nullptr;
    std::string adminProtocol;
    bool adminProtocolSeen = false;
    std::string errorMessage;
    esp_err_t scannerError = ESP_OK;
    size_t responseBytes = 0;
};

static std::string bpp_header_summary(const std::vector<uint8_t>& bytes)
{
    static constexpr char HEX[] = "0123456789ABCDEF";
    std::string out;
    const size_t count = std::min<size_t>(bytes.size(), 8U);
    out.reserve(count * 2U);
    for (size_t i = 0; i < count; ++i) {
        if (i != 0) out.push_back(':');
        out.push_back(HEX[bytes[i] >> 4U]);
        out.push_back(HEX[bytes[i] & 0x0FU]);
    }
    return out.empty() ? std::string("<empty>") : out;
}

static esp_err_t es9_bpp_http_event_handler(esp_http_client_event_t* event)
{
    if (!event || !event->user_data) return ESP_OK;
    auto* capture = static_cast<Es9BppCapture*>(event->user_data);
    if (event->event_id == HTTP_EVENT_ON_HEADER && event->header_key) {
        if (equal_ascii_ci(event->header_key, "X-Admin-Protocol")) {
            capture->adminProtocolSeen = true;
            capture->adminProtocol.assign(event->header_value ? event->header_value : "");
        }
    } else if (event->event_id == HTTP_EVENT_ON_DATA && event->data && event->data_len > 0) {
        const size_t length = static_cast<size_t>(event->data_len);
        if (capture->responseBytes > kMaxBppEncodedBytes + 64U * 1024U ||
            length > kMaxBppEncodedBytes + 64U * 1024U - capture->responseBytes) {
            capture->errorMessage = "ES9+ BPP 响应超过大小上限";
            capture->scannerError = ESP_ERR_INVALID_SIZE;
            return capture->scannerError;
        }
        capture->responseBytes += length;
        if (capture->scanner && capture->scannerError == ESP_OK) {
            capture->scannerError = capture->scanner->feed(static_cast<const char*>(event->data),
                                                            length);
            if (capture->scannerError != ESP_OK) {
                // 只记录有界的阶段、偏移、状态和当前 TLV header，便于定位流式解析错位。
                idf_logf("ES9+ BPP parser: stage=%s err=%s/0x%08X httpBytes=%u b64Chars=%u derBytes=%u derOffset=%u state=%s header=%s segments=%u",
                         capture->scanner->failure_stage(),
                         esp_err_to_name(capture->scannerError),
                         static_cast<unsigned>(capture->scannerError),
                         static_cast<unsigned>(capture->responseBytes),
                         static_cast<unsigned>(capture->scanner->encoded_bpp_chars()),
                         static_cast<unsigned>(capture->scanner->decoded_bpp_bytes()),
                         static_cast<unsigned>(capture->scanner->parser_failure_offset()),
                         capture->scanner->parser_failure_state(),
                         bpp_header_summary(capture->scanner->parser_failure_header()).c_str(),
                         static_cast<unsigned>(capture->scanner->segment_count()));
                if (!capture->scannerMessage || capture->scannerMessage->empty()) {
                    char detail[128];
                    snprintf(detail, sizeof(detail),
                             "ES9+ BPP 响应解析失败（err=%s/0x%08X，responseBytes=%u）",
                             esp_err_to_name(capture->scannerError),
                             static_cast<unsigned>(capture->scannerError),
                             static_cast<unsigned>(capture->responseBytes));
                    capture->errorMessage = detail;
                }
                return capture->scannerError;
            }
        }
    }
    return ESP_OK;
}

static esp_err_t es9_post_json_bpp(const std::string& host,
                                   bool allow_missing_protocol,
                                   const std::string& request_body,
                                   BppJsonStreamScanner& scanner,
                                   std::string& transaction_id,
                                   std::string& message)
{
    clear_string(transaction_id);
    message.clear();
    uint32_t now = static_cast<uint32_t>(time(nullptr));
    if (now < kMinimumValidEpoch) {
        message = "设备时间未同步，不能连接 SM-DP+";
        return ESP_ERR_INVALID_STATE;
    }
    if (host.empty() || host.size() > kMaxHostLength || request_body.empty() ||
        request_body.size() > kMaxEs9JsonBody) {
        message = "ES9+ BPP 请求参数或大小无效";
        return ESP_ERR_INVALID_ARG;
    }

    std::string url = "https://" + host + "/gsma/rsp2/es9plus/getBoundProfilePackage";
    Es9BppCapture capture;
    capture.scanner = &scanner;
    capture.scannerMessage = &message;
    esp_http_client_config_t config = {};
    config.url = url.c_str();
    config.timeout_ms = static_cast<int>(kEs9TimeoutMs);
    config.crt_bundle_attach = esp_crt_bundle_attach;
    config.skip_cert_common_name_check = false;
    config.keep_alive_enable = false;
    config.disable_auto_redirect = true;
    config.buffer_size = 2048;
    config.buffer_size_tx = static_cast<int>(std::min<size_t>(32768U,
        std::max<size_t>(2048U, request_body.size() + 512U)));
    config.event_handler = es9_bpp_http_event_handler;
    config.user_data = &capture;

    esp_http_client_handle_t client = esp_http_client_init(&config);
    if (!client) {
        message = "ES9+ BPP HTTPS 客户端内存不足";
        return ESP_ERR_NO_MEM;
    }
    esp_err_t err = esp_http_client_set_method(client, HTTP_METHOD_POST);
    if (err == ESP_OK) err = esp_http_client_set_header(client, "Content-Type", "application/json");
    if (err == ESP_OK) err = esp_http_client_set_header(client, "User-Agent", "gsma-rsp-lpad");
    if (err == ESP_OK) err = esp_http_client_set_header(client, "X-Admin-Protocol", "gsma/rsp/v2.7.0");
    if (err == ESP_OK) err = esp_http_client_set_post_field(client, request_body.data(),
                                                              request_body.size());
    if (err == ESP_OK) {
        err = esp_http_client_perform(client);
    }
    const int status_code = esp_http_client_get_status_code(client);
    Es9HttpDiagnostics diagnostics = collect_es9_http_diagnostics(client);
    const char* status_state = !scanner.status_seen()
        ? "missing"
        : (scanner.status() == "Executed-Success" ? "success" : "non-success");
    idf_logf("ES9+ GetBPP: HTTP=%d err=%s/0x%08X httpBytes=%u scannerErr=%s/0x%08X status=%s bpp=%d b64Chars=%u derBytes=%u segments=%u protocol=%s",
             status_code, esp_err_to_name(err), static_cast<unsigned>(err),
             static_cast<unsigned>(capture.responseBytes),
             esp_err_to_name(capture.scannerError), static_cast<unsigned>(capture.scannerError),
             status_state, scanner.bpp_seen() ? 1 : 0,
             static_cast<unsigned>(scanner.encoded_bpp_chars()),
             static_cast<unsigned>(scanner.decoded_bpp_bytes()),
             static_cast<unsigned>(scanner.segment_count()),
             rsp_protocol_state(capture.adminProtocol, capture.adminProtocolSeen));
    if (err != ESP_OK && capture.scannerError == ESP_OK) {
        log_es9_http_summary("GetBoundProfilePackage", err, status_code,
                             capture.responseBytes, false, capture.adminProtocol,
                             capture.adminProtocolSeen, diagnostics);
    }
    esp_http_client_cleanup(client);

    if (err != ESP_OK) {
        if (capture.scannerError != ESP_OK && capture.scannerMessage &&
            !capture.scannerMessage->empty()) {
            message = *capture.scannerMessage;
        } else if (!capture.errorMessage.empty() && diagnostics.tlsError == ESP_OK &&
                   diagnostics.transportErrno == 0) {
            message = capture.errorMessage;
        } else {
            set_es9_http_error(message, "GetBPP", err, status_code, diagnostics);
        }
        return err;
    }
    if (status_code != 200) {
        char buf[64];
        snprintf(buf, sizeof(buf), "ES9+ GetBPP HTTP 状态异常（%d）", status_code);
        message = buf;
        return ESP_ERR_INVALID_RESPONSE;
    }
    if (capture.scannerError != ESP_OK) {
        // esp_http_client 可能在回调返回错误后仍以 ESP_OK 结束；此时保留
        // scanner 已写入的具体 Base64/DER/卡侧错误，不降级成笼统文本。
        if (message.empty()) {
            if (!capture.errorMessage.empty()) {
                message = capture.errorMessage;
            } else {
                char detail[128];
                snprintf(detail, sizeof(detail),
                         "ES9+ BPP 响应解析失败（err=%s/0x%08X，responseBytes=%u）",
                         esp_err_to_name(capture.scannerError),
                         static_cast<unsigned>(capture.scannerError),
                         static_cast<unsigned>(capture.responseBytes));
                message = detail;
            }
        }
        return capture.scannerError;
    }
    if (!check_rsp_protocol(capture.adminProtocol, capture.adminProtocolSeen,
                             allow_missing_protocol, "GetBPP", message)) {
        return ESP_ERR_INVALID_RESPONSE;
    }
    err = scanner.finish();
    if (err != ESP_OK) return err;
    if (scanner.status() != "Executed-Success") {
        message = "ES9+ 服务器拒绝请求（";
        message += scanner.status();
        message += "）";
        return ESP_ERR_INVALID_RESPONSE;
    }
    transaction_id = scanner.transaction_id();
    return ESP_OK;
}

static std::string hex_upper(const std::vector<uint8_t>& bytes)
{
    static constexpr char HEX[] = "0123456789ABCDEF";
    std::string out;
    out.reserve(bytes.size() * 2U);
    for (uint8_t byte : bytes) {
        out.push_back(HEX[byte >> 4U]);
        out.push_back(HEX[byte & 0x0FU]);
    }
    return out;
}

static bool build_prepare_download_request(const LpaAuthSession& session,
                                           const std::vector<uint8_t>& hash_cc,
                                           std::vector<uint8_t>& request,
                                           std::string& message)
{
    if (session.smdpSigned2.value.empty() || session.smdpSignature2.value.empty() ||
        session.smdpCertificate.value.empty() ||
        (!hash_cc.empty() && hash_cc.size() != 32U)) {
        message = "PrepareDownload 输入对象不完整";
        return false;
    }
    static constexpr uint8_t TAG_PREPARE_DOWNLOAD[] = {0xBF, 0x21};
    static constexpr uint8_t TAG_HASH_CC[] = {0x04};
    SensitiveBytes body;
    body.value.reserve(session.smdpSigned2.value.size() + session.smdpSignature2.value.size() +
                       session.smdpCertificate.value.size() + hash_cc.size() + 8U);
    body.value.insert(body.value.end(), session.smdpSigned2.value.begin(), session.smdpSigned2.value.end());
    body.value.insert(body.value.end(), session.smdpSignature2.value.begin(), session.smdpSignature2.value.end());
    if (!hash_cc.empty()) idf_esim_internal::append_tlv(body.value, TAG_HASH_CC, hash_cc);
    body.value.insert(body.value.end(), session.smdpCertificate.value.begin(), session.smdpCertificate.value.end());
    clear_sensitive_bytes(request);
    idf_esim_internal::append_tlv(request, TAG_PREPARE_DOWNLOAD, body.value);
    if (request.size() > 16U * 1024U) {
        message = "PrepareDownload 请求对象过大";
        clear_sensitive_bytes(request);
        return false;
    }
    return true;
}

static bool compute_hash_cc(const std::string& confirmation_code,
                            const std::vector<uint8_t>& transaction_id,
                            std::vector<uint8_t>& hash_cc,
                            std::string& message)
{
    hash_cc.clear();
    if (confirmation_code.empty() || transaction_id.empty()) {
        message = "Confirmation Code 或 transactionId 为空";
        return false;
    }
    if (psa_crypto_init() != PSA_SUCCESS) {
        message = "PSA Crypto 初始化失败";
        return false;
    }
    SensitiveBytes first;
    first.value.resize(PSA_HASH_LENGTH(PSA_ALG_SHA_256));
    size_t first_length = 0;
    psa_status_t status = psa_hash_compute(PSA_ALG_SHA_256,
                                           reinterpret_cast<const uint8_t*>(confirmation_code.data()),
                                           confirmation_code.size(), first.value.data(),
                                           first.value.size(), &first_length);
    if (status != PSA_SUCCESS || first_length != first.value.size()) {
        message = "Confirmation Code 哈希失败";
        return false;
    }
    SensitiveBytes input;
    input.value.reserve(first.value.size() + transaction_id.size());
    input.value.insert(input.value.end(), first.value.begin(), first.value.end());
    input.value.insert(input.value.end(), transaction_id.begin(), transaction_id.end());
    hash_cc.resize(PSA_HASH_LENGTH(PSA_ALG_SHA_256));
    size_t output_length = 0;
    status = psa_hash_compute(PSA_ALG_SHA_256, input.value.data(), input.value.size(), hash_cc.data(),
                              hash_cc.size(), &output_length);
    if (status != PSA_SUCCESS || output_length != hash_cc.size()) {
        clear_sensitive_bytes(hash_cc);
        message = "Confirmation Code 哈希失败";
        return false;
    }
    return true;
}

static bool parse_prepare_download_response(const std::vector<uint8_t>& response,
                                            const std::vector<uint8_t>& transaction_id,
                                            std::string& message)
{
    static constexpr uint8_t TAG_PREPARE_DOWNLOAD[] = {0xBF, 0x21};
    static constexpr uint8_t TAG_SUCCESS[] = {0xA0};
    static constexpr uint8_t TAG_ERROR[] = {0xA1};
    static constexpr uint8_t TAG_SEQUENCE[] = {0x30};
    static constexpr uint8_t TAG_SIGNATURE[] = {0x5F, 0x37};
    static constexpr uint8_t TAG_OTPK[] = {0x5F, 0x49};
    static constexpr uint8_t TAG_TRANSACTION[] = {0x80};
    static constexpr uint8_t TAG_INTEGER[] = {0x02};
    idf_esim_internal::Tlv root;
    if (!idf_esim_internal::parse_tlv(response, root, message) ||
        !idf_esim_internal::tag_is(root, TAG_PREPARE_DOWNLOAD)) {
        message = "PrepareDownload 响应 tag 无效";
        return false;
    }
    bool duplicate_success = false;
    bool duplicate_error = false;
    const idf_esim_internal::Tlv* success_choice = unique_child(
        root, TAG_SUCCESS, sizeof(TAG_SUCCESS), duplicate_success);
    const idf_esim_internal::Tlv* error_choice = unique_child(
        root, TAG_ERROR, sizeof(TAG_ERROR), duplicate_error);
    if (duplicate_success || duplicate_error || (success_choice && error_choice)) {
        message = "PrepareDownload 响应分支重复或冲突";
        return false;
    }

    // PrepareDownloadResponseError ::= SEQUENCE {
    //   transactionId [0] TransactionId, downloadErrorCode INTEGER
    // }
    if (error_choice) {
        bool duplicate_error_transaction = false;
        bool duplicate_error_code = false;
        const idf_esim_internal::Tlv* error_transaction = unique_child(
            *error_choice, TAG_TRANSACTION, sizeof(TAG_TRANSACTION), duplicate_error_transaction);
        const idf_esim_internal::Tlv* error_code = unique_child(
            *error_choice, TAG_INTEGER, sizeof(TAG_INTEGER), duplicate_error_code);
        if (duplicate_error_transaction || duplicate_error_code || !error_transaction ||
            !error_code || error_transaction->value != transaction_id || error_code->value.empty() ||
            error_code->value.size() > 4U || (error_code->value.front() & 0x80U) != 0U) {
            message = "PrepareDownload eUICC 错误对象无效";
            return false;
        }
        uint32_t code = 0;
        for (uint8_t byte : error_code->value) code = (code << 8U) | byte;
        char buf[80];
        snprintf(buf, sizeof(buf), "PrepareDownload eUICC 拒绝（错误码=%u）",
                 static_cast<unsigned>(code));
        message = buf;
        return false;
    }

    const idf_esim_internal::Tlv* response_choice = success_choice;
    if (!response_choice) {
        message = "PrepareDownload 响应对象不完整（外层字段=" + safe_tlv_shape(root) + "）";
        return false;
    }

    bool duplicate_signature = false;
    bool duplicate_signed2 = false;
    const idf_esim_internal::Tlv* signature = unique_child(
        *response_choice, TAG_SIGNATURE, sizeof(TAG_SIGNATURE), duplicate_signature);
    const idf_esim_internal::Tlv* signed2 = unique_child(
        *response_choice, TAG_SEQUENCE, sizeof(TAG_SEQUENCE), duplicate_signed2);
    if (duplicate_signature || duplicate_signed2 || !signed2 || !signature ||
        signature->value.empty()) {
        message = "PrepareDownload 响应对象不完整（字段=" +
                  safe_tlv_shape(*response_choice) + "）";
        return false;
    }
    bool duplicate_otpk = false;
    bool duplicate_transaction = false;
    const idf_esim_internal::Tlv* otpk = unique_child(*signed2, TAG_OTPK,
                                                      sizeof(TAG_OTPK), duplicate_otpk);
    const idf_esim_internal::Tlv* transaction = unique_child(*signed2, TAG_TRANSACTION,
                                                             sizeof(TAG_TRANSACTION), duplicate_transaction);
    if (duplicate_otpk || duplicate_transaction || !otpk || otpk->value.empty() ||
        !transaction || transaction->value != transaction_id) {
        message = "PrepareDownload transactionId 不匹配";
        return false;
    }
    return true;
}

static bool parse_profile_installation_result(const std::vector<uint8_t>& pir,
                                              const std::vector<uint8_t>& transaction_id,
                                              const std::string& expected_host,
                                              uint32_t& sequence_number,
                                              std::string& message)
{
    static constexpr uint8_t TAG_PIR[] = {0xBF, 0x37};
    static constexpr uint8_t TAG_DATA[] = {0xBF, 0x27};
    static constexpr uint8_t TAG_METADATA[] = {0xBF, 0x2F};
    static constexpr uint8_t TAG_SMDP_OID[] = {0x06};
    static constexpr uint8_t TAG_TRANSACTION[] = {0x80};
    static constexpr uint8_t TAG_OPERATION[] = {0x81};
    static constexpr uint8_t TAG_ADDRESS[] = {0x0C};
    static constexpr uint8_t TAG_SEQUENCE[] = {0x80};
    static constexpr uint8_t TAG_FINAL_RESULT[] = {0xA2};
    static constexpr uint8_t TAG_SUCCESS[] = {0xA0};
    static constexpr uint8_t TAG_SIGNATURE[] = {0x5F, 0x37};
    idf_esim_internal::Tlv root;
    if (!idf_esim_internal::parse_tlv(pir, root, message) ||
        !idf_esim_internal::tag_is(root, TAG_PIR)) {
        message = "ProfileInstallationResult tag 无效";
        return false;
    }
    bool duplicate_data = false;
    bool duplicate_signature = false;
    const idf_esim_internal::Tlv* data = unique_child(root, TAG_DATA, sizeof(TAG_DATA), duplicate_data);
    const idf_esim_internal::Tlv* signature = unique_child(root, TAG_SIGNATURE,
                                                            sizeof(TAG_SIGNATURE), duplicate_signature);
    if (duplicate_data || duplicate_signature || !data || !signature || signature->value.empty()) {
        message = "ProfileInstallationResult 数据不完整";
        return false;
    }
    bool duplicate_transaction = false;
    bool duplicate_metadata = false;
    bool duplicate_smdp_oid = false;
    bool duplicate_final_result = false;
    const idf_esim_internal::Tlv* transaction = unique_child(
        *data, TAG_TRANSACTION, sizeof(TAG_TRANSACTION), duplicate_transaction);
    const idf_esim_internal::Tlv* metadata = unique_child(
        *data, TAG_METADATA, sizeof(TAG_METADATA), duplicate_metadata);
    const idf_esim_internal::Tlv* smdp_oid = unique_child(
        *data, TAG_SMDP_OID, sizeof(TAG_SMDP_OID), duplicate_smdp_oid);
    const idf_esim_internal::Tlv* final_result = unique_child(
        *data, TAG_FINAL_RESULT, sizeof(TAG_FINAL_RESULT), duplicate_final_result);
    if (duplicate_transaction || duplicate_metadata || duplicate_smdp_oid ||
        duplicate_final_result || !transaction || transaction->value != transaction_id ||
        !metadata || !smdp_oid || smdp_oid->value.empty() || !final_result) {
        message = "ProfileInstallationResult transaction 或结果无效";
        return false;
    }
    bool duplicate_sequence = false;
    bool duplicate_operation = false;
    bool duplicate_address = false;
    const idf_esim_internal::Tlv* seq = unique_child(
        *metadata, TAG_SEQUENCE, sizeof(TAG_SEQUENCE), duplicate_sequence);
    const idf_esim_internal::Tlv* operation = unique_child(
        *metadata, TAG_OPERATION, sizeof(TAG_OPERATION), duplicate_operation);
    const idf_esim_internal::Tlv* address = unique_child(
        *metadata, TAG_ADDRESS, sizeof(TAG_ADDRESS), duplicate_address);
    if (duplicate_sequence || duplicate_operation || duplicate_address || !seq ||
        seq->value.empty() || seq->value.size() > 4U || (seq->value.front() & 0x80U) != 0U ||
        !operation || operation->value.size() != 2U || operation->value[0] > 7U ||
        operation->value[1] != 0x80U || !address || address->value.empty()) {
        message = "ProfileInstallationResult sequence number 无效";
        return false;
    }
    std::string notification_address(reinterpret_cast<const char*>(address->value.data()),
                                     address->value.size());
    if (!is_printable_ascii(notification_address) ||
        lower_ascii_copy(notification_address) != lower_ascii_copy(expected_host)) {
        message = "ProfileInstallationResult notification 地址无效";
        return false;
    }
    sequence_number = 0;
    for (uint8_t byte : seq->value) sequence_number = (sequence_number << 8U) | byte;
    static constexpr uint8_t TAG_AID[] = {0x4F};
    bool duplicate_success = false;
    bool duplicate_aid = false;
    const idf_esim_internal::Tlv* final_choice = unique_child(
        *final_result, TAG_SUCCESS, sizeof(TAG_SUCCESS), duplicate_success);
    const idf_esim_internal::Tlv* aid = final_choice
        ? unique_child(*final_choice, TAG_AID, sizeof(TAG_AID), duplicate_aid)
        : nullptr;
    static constexpr uint8_t TAG_SIMA_RESPONSE[] = {0x04};
    bool duplicate_sima_response = false;
    const idf_esim_internal::Tlv* sima_response = final_choice
        ? unique_child(*final_choice, TAG_SIMA_RESPONSE, sizeof(TAG_SIMA_RESPONSE),
                       duplicate_sima_response)
        : nullptr;
    if (duplicate_success || duplicate_aid || duplicate_sima_response || !final_choice || !aid ||
        !sima_response || aid->value.size() < 5U || aid->value.size() > 16U) {
        message = "ProfileInstallationResult 报告安装失败";
        return false;
    }
    return true;
}

static esp_err_t es9_post_notification(const std::string& host,
                                       bool allow_missing_protocol,
                                       const std::string& request_body,
                                       std::string& message)
{
    uint32_t now = static_cast<uint32_t>(time(nullptr));
    if (now < kMinimumValidEpoch) {
        message = "设备时间未同步，不能连接 SM-DP+";
        return ESP_ERR_INVALID_STATE;
    }
    std::string url = "https://" + host + "/gsma/rsp2/es9plus/handleNotification";
    Es9HttpCapture capture;
    esp_http_client_config_t config = {};
    config.url = url.c_str();
    config.timeout_ms = static_cast<int>(kEs9TimeoutMs);
    config.crt_bundle_attach = esp_crt_bundle_attach;
    config.skip_cert_common_name_check = false;
    config.keep_alive_enable = false;
    config.disable_auto_redirect = true;
    config.buffer_size = 2048;
    config.buffer_size_tx = static_cast<int>(std::min<size_t>(32768U,
        std::max<size_t>(2048U, request_body.size() + 512U)));
    config.event_handler = es9_http_event_handler;
    config.user_data = &capture;
    esp_http_client_handle_t client = esp_http_client_init(&config);
    if (!client) {
        message = "ES9+ HandleNotification HTTPS 客户端内存不足";
        return ESP_ERR_NO_MEM;
    }
    esp_err_t err = esp_http_client_set_method(client, HTTP_METHOD_POST);
    if (err == ESP_OK) err = esp_http_client_set_header(client, "Content-Type", "application/json");
    if (err == ESP_OK) err = esp_http_client_set_header(client, "User-Agent", "gsma-rsp-lpad");
    if (err == ESP_OK) err = esp_http_client_set_header(client, "X-Admin-Protocol", "gsma/rsp/v2.7.0");
    if (err == ESP_OK) err = esp_http_client_set_post_field(client, request_body.data(),
                                                              request_body.size());
    if (err == ESP_OK) err = esp_http_client_perform(client);
    const int status_code = esp_http_client_get_status_code(client);
    Es9HttpDiagnostics diagnostics = collect_es9_http_diagnostics(client);
    esp_http_client_cleanup(client);
    if (err != ESP_OK) {
        set_es9_http_error(message, "HandleNotification", err, status_code, diagnostics);
        return err;
    }
    if (status_code != 200 && status_code != 204) {
        char buf[64];
        snprintf(buf, sizeof(buf), "ES9+ HandleNotification HTTP 状态异常（%d）", status_code);
        message = buf;
        return ESP_ERR_INVALID_RESPONSE;
    }
    if (capture.bodyOverflow) {
        message = "ES9+ HandleNotification 响应超过大小上限";
        return ESP_ERR_INVALID_SIZE;
    }
    if (!check_rsp_protocol(capture.adminProtocol, capture.adminProtocolSeen,
                             allow_missing_protocol, "HandleNotification", message)) {
        return ESP_ERR_INVALID_RESPONSE;
    }
    if (status_code == 200 && !capture.body.empty() &&
        !parse_success_status(capture.body, message)) {
        return ESP_ERR_INVALID_RESPONSE;
    }
    return ESP_OK;
}

struct DownloadStatsGuard {
    explicit DownloadStatsGuard(LpaDownloadStats& value) : stats(value)
    {
        stats.freeHeapAtStart = heap_caps_get_free_size(MALLOC_CAP_8BIT);
        sample_heap(stats);
    }
    ~DownloadStatsGuard()
    {
        stats.freeHeapAtEnd = heap_caps_get_free_size(MALLOC_CAP_8BIT);
        sample_heap(stats);
    }
    LpaDownloadStats& stats;
};

}  // namespace

esp_err_t idf_lpa_run_profile_download(const LpaActivationCode& activation_code,
                                       const LpaDownloadObserver& observer,
                                       LpaDownloadStats& stats,
                                       std::string& safe_message)
{
    stats = LpaDownloadStats();
    safe_message.clear();
    DownloadStatsGuard stats_guard(stats);
    auto failed = [&](esp_err_t err) -> esp_err_t {
        download_phase(observer, "failed", safe_message.c_str());
        return err;
    };
    if (activation_code.smdpHost.empty() || activation_code.matchingId.empty()) {
        safe_message = "Activation Code 输入不完整";
        return failed(ESP_ERR_INVALID_ARG);
    }
    download_phase(observer, "authentication", "正在完成 SM-DP+ 认证");
    LpaAuthenticationResult auth_result;
    LpaAuthSession session;
    esp_err_t err = run_authentication_session(activation_code,
                                                observer.allow_missing_admin_protocol,
                                                auth_result, session, safe_message);
    sample_heap(stats);
    if (err != ESP_OK) return failed(err);

    SensitiveBytes hash_cc;
    if (auth_result.confirmationCodeRequired) {
        download_phase(observer, "waiting_confirmation", "请输入 Confirmation Code");
        if (!observer.wait_confirmation_code) {
            safe_message = "服务器要求 Confirmation Code";
            return failed(ESP_ERR_INVALID_STATE);
        }
        SensitiveText confirmation_code;
        err = observer.wait_confirmation_code(observer.context, confirmation_code.text, safe_message);
        if (err != ESP_OK) return failed(err);
        if (confirmation_code.text.empty()) {
            safe_message = "Confirmation Code 不能为空";
            return failed(ESP_ERR_INVALID_ARG);
        }
        if (!compute_hash_cc(confirmation_code.text, session.transactionId.value, hash_cc.value,
                             safe_message)) {
            return failed(ESP_ERR_INVALID_ARG);
        }
        clear_string(confirmation_code.text);
    }
    download_phase(observer, "prepare_download", "正在准备 eUICC 下载会话");
    SensitiveBytes prepare_request;
    if (!build_prepare_download_request(session, hash_cc.value, prepare_request.value, safe_message)) {
        return failed(ESP_ERR_INVALID_ARG);
    }
    SensitiveBytes prepare_response;
    err = idf_esim_lpa_prepare_download(prepare_request.value, prepare_response.value, safe_message);
    clear_sensitive_bytes(prepare_request.value);
    if (err != ESP_OK) return failed(err);
    if (!parse_prepare_download_response(prepare_response.value, session.transactionId.value,
                                         safe_message)) {
        return failed(ESP_ERR_INVALID_RESPONSE);
    }
    session.prepareDownloadResponse.value = std::move(prepare_response.value);
    sample_heap(stats);

    SensitiveText prepare_b64;
    if (!base64_encode_bytes(session.prepareDownloadResponse.value, prepare_b64.text,
                             safe_message)) {
        return failed(ESP_ERR_INVALID_SIZE);
    }
    SensitiveText get_bpp_request;
    SensitiveText transaction_hex;
    hex_upper(session.transactionId.value).swap(transaction_hex.text);
    bool first = true;
    get_bpp_request.text.push_back('{');
    append_json_field(get_bpp_request.text, "transactionId", transaction_hex.text, first);
    append_json_field(get_bpp_request.text, "prepareDownloadResponse", prepare_b64.text, first);
    get_bpp_request.text.push_back('}');
    clear_string(prepare_b64.text);

    download_phase(observer, "get_bpp", "正在获取并写入 Profile");
    BppStreamParser bpp_parser;
    BppJsonStreamScanner bpp_json(bpp_parser, safe_message);
    SensitiveText response_transaction_id;
    err = es9_post_json_bpp(activation_code.smdpHost,
                            observer.allow_missing_admin_protocol,
                            get_bpp_request.text, bpp_json,
                            response_transaction_id.text, safe_message);
    clear_string(get_bpp_request.text);
    if (err != ESP_OK) return failed(err);
    stats.bppEncodedBytes = bpp_json.encoded_bpp_chars();
    stats.bppDecodedBytes = bpp_parser.decoded_bytes();
    SensitiveBytes response_transaction;
    if (response_transaction_id.text.empty() ||
        !decode_transaction_id(response_transaction_id.text, response_transaction.value, safe_message) ||
        response_transaction.value != session.transactionId.value) {
        safe_message = "ES9+ GetBPP transactionId 不匹配";
        return failed(ESP_ERR_INVALID_RESPONSE);
    }
    if (bpp_parser.installation_result().empty()) {
        safe_message = "eUICC 未返回 ProfileInstallationResult";
        return failed(ESP_ERR_INVALID_RESPONSE);
    }
    SensitiveBytes pir;
    pir.value = bpp_parser.installation_result();
    uint32_t sequence_number = 0;
    if (!parse_profile_installation_result(pir.value, session.transactionId.value,
                                           activation_code.smdpHost, sequence_number,
                                           safe_message)) {
        return failed(ESP_ERR_INVALID_RESPONSE);
    }
    sample_heap(stats);

    download_phase(observer, "notify", "正在向 SM-DP+ 确认安装结果");
    SensitiveText pir_b64;
    if (!base64_encode_bytes(pir.value, pir_b64.text, safe_message)) {
        return failed(ESP_ERR_INVALID_SIZE);
    }
    SensitiveText notification_request;
    first = true;
    notification_request.text.push_back('{');
    append_json_field(notification_request.text, "pendingNotification", pir_b64.text, first);
    notification_request.text.push_back('}');
    clear_string(pir_b64.text);
    err = es9_post_notification(activation_code.smdpHost,
                                observer.allow_missing_admin_protocol,
                                notification_request.text, safe_message);
    clear_string(notification_request.text);
    if (err != ESP_OK) return failed(err);

    download_phase(observer, "remove_notification", "正在清理 eUICC 通知");
    err = idf_esim_lpa_remove_notification(sequence_number, safe_message);
    if (err != ESP_OK) return failed(err);
    download_phase(observer, "complete", "Profile 安装完成，未自动启用");
    safe_message = "Profile 安装完成，请按需显式启用";
    return ESP_OK;
}
