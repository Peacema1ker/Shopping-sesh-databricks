#include <algorithm>
#include <atomic>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <mutex>
#include <string>
#include <string_view>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace fs = std::filesystem;

static constexpr int NUM_BUCKETS = 64;
static constexpr int64_t MS_PER_SEC = 1000LL;
static constexpr int64_t MS_PER_DAY = 86400000LL;
static constexpr int64_t MS_30_MIN = 1800000LL;
static constexpr int64_t MS_7_DAYS = 7LL * MS_PER_DAY;

// FNV-1a 64-bit hash
static inline uint64_t hash_sv(std::string_view sv) {
    uint64_t h = 14695981039346656037ULL;
    for (unsigned char c : sv) {
        h ^= c;
        h *= 1099511628211ULL;
    }
    // Mix high bits into low bits
    h ^= h >> 33;
    h *= 0xff51afd7ed558ccdULL;
    h ^= h >> 33;
    return h;
}

static inline int64_t floor_div(int64_t a, int64_t b) {
    int64_t q = a / b;
    int64_t r = a % b;
    if (r != 0 && ((r < 0) != (b < 0))) --q;
    return q;
}

// Strict CSV parser according to rules.md:
// - Lines already split strictly on '\n' (do NOT strip '\r')
// - Empty line is malformed
// - Exact N fields (N-1 commas)
// - Any '"' only allowed wrapping the entire field; no '"' inside
static inline bool parse_csv_line(std::string_view line, int expected_fields, std::string_view* out) {
    if (line.empty()) return false;
    int idx = 0;
    size_t start = 0;
    const size_t n = line.size();
    for (size_t i = 0; i <= n; ++i) {
        if (i == n || line[i] == ',') {
            if (idx >= expected_fields) return false;
            std::string_view f = line.substr(start, i - start);
            // Check quotes
            size_t first_q = f.find('"');
            if (first_q != std::string_view::npos) {
                if (f.size() < 2 || first_q != 0 || f.back() != '"') return false;
                if (f.find('"', 1) != f.size() - 1) return false;
                f = f.substr(1, f.size() - 2);
            }
            out[idx++] = f;
            start = i + 1;
        }
    }
    return idx == expected_fields;
}

static inline bool is_ascii_digit(char c) {
    return c >= '0' && c <= '9';
}

static inline bool parse_2d(const char* p, int& v) {
    if (!is_ascii_digit(p[0]) || !is_ascii_digit(p[1])) return false;
    v = (p[0] - '0') * 10 + (p[1] - '0');
    return true;
}

static inline bool parse_4d(const char* p, int& v) {
    if (!is_ascii_digit(p[0]) || !is_ascii_digit(p[1]) || !is_ascii_digit(p[2]) || !is_ascii_digit(p[3])) return false;
    v = (p[0] - '0') * 1000 + (p[1] - '0') * 100 + (p[2] - '0') * 10 + (p[3] - '0');
    return true;
}

static inline bool is_leap(int y) {
    return (y % 4 == 0 && y % 100 != 0) || (y % 400 == 0);
}

static inline int days_in_month(int y, int m) {
    static constexpr int dm[13] = {0,31,28,31,30,31,30,31,31,30,31,30,31};
    if (m == 2 && is_leap(y)) return 29;
    return dm[m];
}

// Howard Hinnant's days_from_civil
static inline int64_t days_from_civil(int64_t y, unsigned m, unsigned d) {
    y -= m <= 2;
    const int64_t era = (y >= 0 ? y : y - 399) / 400;
    const unsigned yoe = static_cast<unsigned>(y - era * 400);
    const unsigned doy = (153 * (m + (m > 2 ? -3 : 9)) + 2) / 5 + d - 1;
    const unsigned doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    return era * 146097 + static_cast<int64_t>(doe) - 719468;
}

static inline bool parse_iso_prefix(const char* p, int64_t& local_ms) {
    if (p[4] != '-' || p[7] != '-' || p[10] != 'T' || p[13] != ':' || p[16] != ':') return false;
    int Y, M, D, h, m, s;
    if (!parse_4d(p, Y) || !parse_2d(p + 5, M) || !parse_2d(p + 8, D) ||
        !parse_2d(p + 11, h) || !parse_2d(p + 14, m) || !parse_2d(p + 17, s)) {
        return false;
    }
    if (M < 1 || M > 12) return false;
    if (D < 1 || D > days_in_month(Y, M)) return false;
    if (h < 0 || h > 23 || m < 0 || m > 59 || s < 0 || s > 59) return false;
    int64_t days = days_from_civil(Y, static_cast<unsigned>(M), static_cast<unsigned>(D));
    local_ms = (days * 86400LL + h * 3600LL + m * 60LL + s) * 1000LL;
    return true;
}

static inline bool parse_f1_ts(std::string_view sv, int64_t& out_ms) {
    if (sv.size() != 20 || sv[19] != 'Z') return false;
    return parse_iso_prefix(sv.data(), out_ms);
}

// Returns true iff valid F1/F2/F3 AND min_ms <= out_ms < max_ms
static inline bool parse_ts_in_window(std::string_view sv, int64_t min_ms, int64_t max_ms, int64_t& out_ms) {
    const size_t n = sv.size();
    if (n == 0) return false;
    const char* p = sv.data();
    // F1: 20 chars ending in 'Z'
    if (n == 20 && p[19] == 'Z') {
        if (!parse_iso_prefix(p, out_ms)) return false;
        return out_ms >= min_ms && out_ms < max_ms;
    }
    // F2: 25 chars with +HH:MM or -HH:MM
    if (n == 25 && (p[19] == '+' || p[19] == '-') && p[22] == ':') {
        int64_t local_ms = 0;
        if (!parse_iso_prefix(p, local_ms)) return false;
        int oh, om;
        if (!parse_2d(p + 20, oh) || !parse_2d(p + 23, om)) return false;
        if (oh < 0 || oh > 23 || om < 0 || om > 59) return false;
        int64_t off_ms = (oh * 3600LL + om * 60LL) * 1000LL;
        out_ms = (p[19] == '+') ? (local_ms - off_ms) : (local_ms + off_ms);
        return out_ms >= min_ms && out_ms < max_ms;
    }
    // F3: ASCII digits only
    // Check all digits first; track value with cap above max_ms to handle arbitrary length
    uint64_t val = 0;
    bool overflow = false;
    for (size_t i = 0; i < n; ++i) {
        char c = p[i];
        if (!is_ascii_digit(c)) return false;
        if (!overflow) {
            if (val > 900000000000000000ULL) {
                overflow = true;
            } else {
                val = val * 10ULL + static_cast<uint64_t>(c - '0');
            }
        }
    }
    if (overflow) return false;
    out_ms = static_cast<int64_t>(val);
    return out_ms >= min_ms && out_ms < max_ms;
}

static inline bool parse_price_cents(std::string_view sv, uint32_t& out_price) {
    if (sv.empty()) return false;
    uint64_t val = 0;
    for (char c : sv) {
        if (!is_ascii_digit(c)) return false;
        if (val <= 10000000ULL) {
            val = val * 10ULL + static_cast<uint64_t>(c - '0');
        }
    }
    if (val < 1ULL || val > 10000000ULL) return false;
    out_price = static_cast<uint32_t>(val);
    return true;
}

static std::vector<std::string> list_csv_files(const fs::path& dir) {
    std::vector<std::string> files;
    if (!fs::exists(dir)) return files;
    for (const auto& entry : fs::directory_iterator(dir)) {
        if (!entry.is_regular_file()) continue;
        std::string name = entry.path().filename().string();
        if (name.empty() || name[0] == '.') continue;
        if (name.size() >= 4 && name.compare(name.size() - 4, 4, ".csv") == 0) {
            files.push_back(entry.path().string());
        }
    }
    std::sort(files.begin(), files.end());
    return files;
}

// Fast buffered line reader that splits strictly on '\n' (never strips '\r')
class FastLineReader {
public:
    explicit FastLineReader(const std::string& path) : fp_(std::fopen(path.c_str(), "rb")) {
        buf_.resize(1 << 18); // 256 KB
    }
    ~FastLineReader() {
        if (fp_) std::fclose(fp_);
    }
    bool ok() const { return fp_ != nullptr; }

    bool next_line(std::string& out) {
        out.clear();
        if (!fp_) return false;
        while (true) {
            if (pos_ < len_) {
                const char* start = buf_.data() + pos_;
                const void* nl = std::memchr(start, '\n', len_ - pos_);
                if (nl) {
                    size_t chunk = static_cast<const char*>(nl) - start;
                    out.append(start, chunk);
                    pos_ += chunk + 1;
                    return true;
                } else {
                    out.append(start, len_ - pos_);
                    pos_ = len_;
                }
            }
            len_ = std::fread(buf_.data(), 1, buf_.size(), fp_);
            pos_ = 0;
            if (len_ == 0) {
                return !out.empty();
            }
        }
    }

private:
    FILE* fp_ = nullptr;
    std::vector<char> buf_;
    size_t pos_ = 0;
    size_t len_ = 0;
};

// Buffered thread-safe bucket writer
class BucketWriters {
public:
    BucketWriters(const std::string& prefix, int num_buckets) : files_(num_buckets), mutexes_(num_buckets) {
        for (int i = 0; i < num_buckets; ++i) {
            std::string p = prefix + "_" + std::to_string(i) + ".bin";
            files_[i] = std::fopen(p.c_str(), "wb");
            if (!files_[i]) {
                std::fprintf(stderr, "Failed to open bucket file: %s\n", p.c_str());
                std::exit(1);
            }
            std::setvbuf(files_[i], nullptr, _IOFBF, 1 << 16);
        }
    }
    ~BucketWriters() { close_all(); }

    void append(int bucket, const char* data, size_t size) {
        if (size == 0) return;
        std::lock_guard<std::mutex> lk(mutexes_[bucket]);
        std::fwrite(data, 1, size, files_[bucket]);
    }

    void close_all() {
        for (auto& fp : files_) {
            if (fp) {
                std::fclose(fp);
                fp = nullptr;
            }
        }
    }

private:
    std::vector<FILE*> files_;
    std::vector<std::mutex> mutexes_;
};

// Union-Find for Linked IDs
struct LinkResolver {
    std::unordered_map<std::string, uint32_t> str_to_id;
    std::vector<std::string> id_to_str;
    std::vector<uint32_t> parent;
    std::vector<uint32_t> sz;
    std::vector<uint32_t> min_id; // byte-wise smallest string id in component

    uint32_t get_or_add(std::string_view sv) {
        std::string s(sv);
        auto it = str_to_id.find(s);
        if (it != str_to_id.end()) return it->second;
        uint32_t id = static_cast<uint32_t>(id_to_str.size());
        str_to_id.emplace(s, id);
        id_to_str.push_back(std::move(s));
        parent.push_back(id);
        sz.push_back(1);
        min_id.push_back(id);
        return id;
    }

    uint32_t find(uint32_t x) {
        while (parent[x] != x) {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        return x;
    }

    void unite(uint32_t a, uint32_t b) {
        uint32_t ra = find(a);
        uint32_t rb = find(b);
        if (ra == rb) return;
        if (sz[ra] < sz[rb]) std::swap(ra, rb);
        parent[rb] = ra;
        sz[ra] += sz[rb];
        if (id_to_str[min_id[rb]] < id_to_str[min_id[ra]]) {
            min_id[ra] = min_id[rb];
        }
    }

    // Finalize so every node points directly to its canonical string id
    std::vector<uint32_t> canon_id;
    void finalize() {
        canon_id.resize(id_to_str.size());
        for (uint32_t i = 0; i < id_to_str.size(); ++i) {
            canon_id[i] = min_id[find(i)];
        }
        parent.clear(); parent.shrink_to_fit();
        sz.clear(); sz.shrink_to_fit();
        min_id.clear(); min_id.shrink_to_fit();
    }

    // Thread-safe after finalize()
    std::string_view resolve(std::string_view uid, std::string& tmp_key) const {
        if (str_to_id.empty()) return uid;
        tmp_key.assign(uid.data(), uid.size());
        auto it = str_to_id.find(tmp_key);
        if (it == str_to_id.end()) return uid;
        return id_to_str[canon_id[it->second]];
    }
};

static bool extract_json_string(const std::string& json, const std::string& key, std::string& out) {
    std::string pattern = "\"" + key + "\"";
    size_t pos = json.find(pattern);
    if (pos == std::string::npos) return false;
    pos = json.find(':', pos + pattern.size());
    if (pos == std::string::npos) return false;
    pos = json.find('"', pos + 1);
    if (pos == std::string::npos) return false;
    size_t end = json.find('"', pos + 1);
    if (end == std::string::npos) return false;
    out = json.substr(pos + 1, end - pos - 1);
    return true;
}

template <typename T>
static inline void append_pod(std::string& buf, const T& v) {
    buf.append(reinterpret_cast<const char*>(&v), sizeof(T));
}

template <typename T>
static inline bool read_pod(const char*& p, const char* end, T& v) {
    if (static_cast<size_t>(end - p) < sizeof(T)) return false;
    std::memcpy(&v, p, sizeof(T));
    p += sizeof(T);
    return true;
}

struct CampDayKey {
    uint32_t camp_idx;
    int32_t day;
    bool operator==(const CampDayKey& o) const { return camp_idx == o.camp_idx && day == o.day; }
};

struct CampDayHash {
    size_t operator()(const CampDayKey& k) const {
        return (static_cast<uint64_t>(k.camp_idx) << 32) ^ static_cast<uint32_t>(k.day);
    }
};

struct CampStats {
    int64_t sessions = 0;
    int64_t purchasing_sessions = 0;
    int64_t revenue_cents = 0;
    int64_t assisted_sessions = 0;
};

int main() {
    const char* env_data = std::getenv("DATA_DIR");
    const char* env_scratch = std::getenv("SCRATCH_DIR");
    const char* env_ncpu = std::getenv("NCPU");

    fs::path data_dir = env_data ? env_data : "/data";
    fs::path scratch_dir = env_scratch ? env_scratch : "/scratch";
    int ncpu = env_ncpu ? std::atoi(env_ncpu) : 8;
    if (ncpu < 1) ncpu = 1;
    if (ncpu > 32) ncpu = 32;

    fs::create_directories(scratch_dir);

    // 1. Read manifest.json
    int64_t window_start = 0, window_end = 0;
    {
        std::ifstream mf(data_dir / "manifest.json");
        if (!mf) {
            std::fprintf(stderr, "Failed to open manifest.json\n");
            return 1;
        }
        std::string content((std::istreambuf_iterator<char>(mf)), std::istreambuf_iterator<char>());
        std::string ws_str, we_str;
        if (!extract_json_string(content, "window_start", ws_str) ||
            !extract_json_string(content, "window_end", we_str) ||
            !parse_f1_ts(ws_str, window_start) ||
            !parse_f1_ts(we_str, window_end)) {
            std::fprintf(stderr, "Failed to parse manifest.json\n");
            return 1;
        }
    }
    const int64_t click_window_start = window_start - MS_7_DAYS;

    // 2. Read products.csv -> sorted categories (so cat_id order == byte-wise string order!)
    std::vector<std::string> cat_names;
    std::unordered_map<std::string, uint16_t> prod_to_cat;
    uint16_t unknown_cat_id = 0;
    {
        std::vector<std::pair<std::string, std::string>> prod_rows;
        std::unordered_set<std::string> cat_set;
        cat_set.insert("unknown");
        FastLineReader reader((data_dir / "products.csv").string());
        std::string line;
        if (reader.ok() && reader.next_line(line)) { // skip header
            std::string_view fields[2];
            while (reader.next_line(line)) {
                if (parse_csv_line(line, 2, fields) && !fields[0].empty()) {
                    std::string pid(fields[0]);
                    std::string cat(fields[1]);
                    cat_set.insert(cat);
                    prod_rows.emplace_back(std::move(pid), std::move(cat));
                }
            }
        }
        cat_names.assign(cat_set.begin(), cat_set.end());
        std::sort(cat_names.begin(), cat_names.end());
        std::unordered_map<std::string, uint16_t> cat_to_id;
        for (size_t i = 0; i < cat_names.size(); ++i) {
            cat_to_id[cat_names[i]] = static_cast<uint16_t>(i);
        }
        unknown_cat_id = cat_to_id["unknown"];
        prod_to_cat.reserve(prod_rows.size() * 2 + 16);
        for (auto& pr : prod_rows) {
            prod_to_cat.emplace(std::move(pr.first), cat_to_id[pr.second]);
        }
    }

    // 3. Read campaigns.csv (camp_idx = 0 is reserved for "organic")
    std::vector<std::string> camp_ids = {"organic"};
    std::vector<std::string> camp_channels = {"organic"};
    std::unordered_map<std::string, uint32_t> camp_to_idx;
    {
        FastLineReader reader((data_dir / "campaigns.csv").string());
        std::string line;
        if (reader.ok() && reader.next_line(line)) { // skip header
            std::string_view fields[2];
            while (reader.next_line(line)) {
                if (parse_csv_line(line, 2, fields) && !fields[0].empty()) {
                    uint32_t idx = static_cast<uint32_t>(camp_ids.size());
                    std::string cid(fields[0]);
                    camp_to_idx.emplace(cid, idx);
                    camp_ids.push_back(std::move(cid));
                    camp_channels.emplace_back(fields[1]);
                }
            }
        }
    }
    const size_t num_campaigns = camp_ids.size();

    // 4. Read links/*.csv and build Union-Find
    LinkResolver links;
    {
        auto link_files = list_csv_files(data_dir / "links");
        std::string line;
        std::string_view fields[2];
        for (const auto& f : link_files) {
            FastLineReader reader(f);
            if (!reader.ok() || !reader.next_line(line)) continue; // skip header
            while (reader.next_line(line)) {
                if (!parse_csv_line(line, 2, fields)) continue;
                if (fields[0].empty() || fields[1].empty()) continue;
                uint32_t a = links.get_or_add(fields[0]);
                uint32_t b = links.get_or_add(fields[1]);
                links.unite(a, b);
            }
        }
        links.finalize();
    }

    // 5. Phase 1: Parse events/*.csv in parallel -> hash-partition by event_id into NUM_BUCKETS
    {
        auto event_files = list_csv_files(data_dir / "events");
        BucketWriters ev_writers((scratch_dir / "ev_dedup").string(), NUM_BUCKETS);
        std::atomic<size_t> next_file{0};

        auto worker = [&]() {
            std::vector<std::string> local_bufs(NUM_BUCKETS);
            for (auto& b : local_bufs) b.reserve(65536);
            std::string line;
            std::string tmp_key;
            std::string_view fields[7];

            auto flush_bucket = [&](int b) {
                ev_writers.append(b, local_bufs[b].data(), local_bufs[b].size());
                local_bufs[b].clear();
            };

            while (true) {
                size_t fi = next_file.fetch_add(1);
                if (fi >= event_files.size()) break;
                FastLineReader reader(event_files[fi]);
                if (!reader.ok() || !reader.next_line(line)) continue; // skip header
                while (reader.next_line(line)) {
                    if (!parse_csv_line(line, 7, fields)) continue;
                    std::string_view eid = fields[0];
                    if (eid.empty()) continue;

                    int64_t ingest_ts = 0;
                    if (!parse_f1_ts(fields[3], ingest_ts)) continue;

                    // Validate row (remember: invalid copy with smallest ingest_ts kills later valid copies!)
                    bool valid = true;
                    std::string_view uid = fields[1];
                    int64_t ts = 0;
                    uint8_t is_purchase = 0;
                    uint32_t price_cents = 0;
                    uint16_t cat_id = unknown_cat_id;

                    if (uid.empty() || fields[5].empty()) {
                        valid = false;
                    } else if (!parse_ts_in_window(fields[2], window_start, window_end, ts)) {
                        valid = false;
                    } else if (ingest_ts - ts > MS_PER_DAY) {
                        valid = false;
                    } else {
                        std::string_view et = fields[4];
                        if (et == "purchase") {
                            is_purchase = 1;
                            if (!parse_price_cents(fields[6], price_cents)) {
                                valid = false;
                            }
                        } else if (et == "view" || et == "cart") {
                            is_purchase = 0;
                        } else {
                            valid = false;
                        }
                    }

                    int b = static_cast<int>(hash_sv(eid) & (NUM_BUCKETS - 1));
                    std::string& buf = local_bufs[b];
                    uint32_t eid_len = static_cast<uint32_t>(eid.size());
                    append_pod(buf, eid_len);
                    buf.append(eid.data(), eid.size());
                    append_pod(buf, ingest_ts);

                    if (!valid) {
                        uint8_t flags = 0;
                        append_pod(buf, flags);
                    } else {
                        uint8_t flags = static_cast<uint8_t>(1 | (is_purchase << 1));
                        append_pod(buf, flags);
                        if (is_purchase) {
                            tmp_key.assign(fields[5].data(), fields[5].size());
                            auto pit = prod_to_cat.find(tmp_key);
                            if (pit != prod_to_cat.end()) cat_id = pit->second;
                        }
                        std::string_view canon_uid = links.resolve(uid, tmp_key);
                        append_pod(buf, ts);
                        append_pod(buf, price_cents);
                        append_pod(buf, cat_id);
                        uint32_t uid_len = static_cast<uint32_t>(canon_uid.size());
                        append_pod(buf, uid_len);
                        buf.append(canon_uid.data(), canon_uid.size());
                    }

                    if (buf.size() >= 60000) flush_bucket(b);
                }
            }
            for (int b = 0; b < NUM_BUCKETS; ++b) flush_bucket(b);
        };

        std::vector<std::thread> threads;
        for (int t = 0; t < ncpu; ++t) threads.emplace_back(worker);
        for (auto& th : threads) th.join();
        ev_writers.close_all();
    }

    // 6. Phase 2: Deduplicate each ev_dedup bucket in parallel -> route surviving events to user_ev buckets
    {
        BucketWriters user_ev_writers((scratch_dir / "user_ev").string(), NUM_BUCKETS);
        std::atomic<int> next_bucket{0};

        struct DedupVal {
            int64_t ingest_ts;
            int64_t ts;
            uint32_t price_cents;
            uint16_t cat_id;
            uint8_t flags; // bit 0: valid, bit 1: is_purchase
            uint32_t uid_off;
            uint32_t uid_len;
        };

        auto worker = [&]() {
            std::vector<std::string> local_bufs(NUM_BUCKETS);
            for (auto& b : local_bufs) b.reserve(65536);

            auto flush_bucket = [&](int b) {
                user_ev_writers.append(b, local_bufs[b].data(), local_bufs[b].size());
                local_bufs[b].clear();
            };

            while (true) {
                int b = next_bucket.fetch_add(1);
                if (b >= NUM_BUCKETS) break;
                std::string path = (scratch_dir / ("ev_dedup_" + std::to_string(b) + ".bin")).string();
                std::ifstream in(path, std::ios::binary | std::ios::ate);
                if (!in) continue;
                size_t fsize = static_cast<size_t>(in.tellg());
                if (fsize == 0) {
                    in.close();
                    fs::remove(path);
                    continue;
                }
                std::string raw(fsize, '\0');
                in.seekg(0);
                in.read(raw.data(), fsize);
                in.close();
                fs::remove(path);

                std::unordered_map<std::string_view, DedupVal> dedup;
                dedup.reserve(fsize / 50 + 1024);

                const char* p = raw.data();
                const char* end = raw.data() + raw.size();
                while (p < end) {
                    uint32_t eid_len = 0;
                    if (!read_pod(p, end, eid_len)) break;
                    std::string_view eid(p, eid_len);
                    p += eid_len;
                    int64_t ingest_ts = 0;
                    uint8_t flags = 0;
                    read_pod(p, end, ingest_ts);
                    read_pod(p, end, flags);

                    int64_t ts = 0;
                    uint32_t price_cents = 0;
                    uint16_t cat_id = 0;
                    uint32_t uid_off = 0, uid_len = 0;
                    if (flags & 1) {
                        read_pod(p, end, ts);
                        read_pod(p, end, price_cents);
                        read_pod(p, end, cat_id);
                        read_pod(p, end, uid_len);
                        uid_off = static_cast<uint32_t>(p - raw.data());
                        p += uid_len;
                    }

                    auto it = dedup.find(eid);
                    if (it == dedup.end()) {
                        dedup.emplace(eid, DedupVal{ingest_ts, ts, price_cents, cat_id, flags, uid_off, uid_len});
                    } else if (ingest_ts < it->second.ingest_ts) {
                        it->second = DedupVal{ingest_ts, ts, price_cents, cat_id, flags, uid_off, uid_len};
                    }
                }

                for (const auto& kv : dedup) {
                    const DedupVal& v = kv.second;
                    if (!(v.flags & 1)) continue; // invalid or late
                    std::string_view uid(raw.data() + v.uid_off, v.uid_len);
                    int ub = static_cast<int>(hash_sv(uid) & (NUM_BUCKETS - 1));
                    std::string& buf = local_bufs[ub];
                    append_pod(buf, v.uid_len);
                    buf.append(uid.data(), v.uid_len);
                    append_pod(buf, v.ts);
                    append_pod(buf, v.price_cents);
                    append_pod(buf, v.cat_id);
                    uint8_t is_purch = (v.flags >> 1) & 1;
                    append_pod(buf, is_purch);
                    if (buf.size() >= 60000) flush_bucket(ub);
                }
            }
            for (int ub = 0; ub < NUM_BUCKETS; ++ub) flush_bucket(ub);
        };

        std::vector<std::thread> threads;
        for (int t = 0; t < ncpu; ++t) threads.emplace_back(worker);
        for (auto& th : threads) th.join();
        user_ev_writers.close_all();
    }

    // 7. Phase 3: Parse clicks/*.csv in parallel -> validate & route to user_cl buckets
    {
        auto click_files = list_csv_files(data_dir / "clicks");
        BucketWriters user_cl_writers((scratch_dir / "user_cl").string(), NUM_BUCKETS);
        std::atomic<size_t> next_file{0};

        auto worker = [&]() {
            std::vector<std::string> local_bufs(NUM_BUCKETS);
            for (auto& b : local_bufs) b.reserve(65536);
            std::string line;
            std::string tmp_key;
            std::string_view fields[4];

            auto flush_bucket = [&](int b) {
                user_cl_writers.append(b, local_bufs[b].data(), local_bufs[b].size());
                local_bufs[b].clear();
            };

            while (true) {
                size_t fi = next_file.fetch_add(1);
                if (fi >= click_files.size()) break;
                FastLineReader reader(click_files[fi]);
                if (!reader.ok() || !reader.next_line(line)) continue; // skip header
                while (reader.next_line(line)) {
                    if (!parse_csv_line(line, 4, fields)) continue;
                    std::string_view cid = fields[0];
                    std::string_view uid = fields[1];
                    std::string_view camp = fields[2];
                    if (cid.empty() || uid.empty() || camp.empty()) continue;

                    int64_t ts = 0;
                    if (!parse_ts_in_window(fields[3], click_window_start, window_end, ts)) continue;

                    tmp_key.assign(camp.data(), camp.size());
                    auto cit = camp_to_idx.find(tmp_key);
                    if (cit == camp_to_idx.end()) continue;
                    uint32_t camp_idx = cit->second;

                    std::string_view canon_uid = links.resolve(uid, tmp_key);
                    int ub = static_cast<int>(hash_sv(canon_uid) & (NUM_BUCKETS - 1));
                    std::string& buf = local_bufs[ub];
                    uint32_t uid_len = static_cast<uint32_t>(canon_uid.size());
                    uint32_t cid_len = static_cast<uint32_t>(cid.size());
                    append_pod(buf, uid_len);
                    buf.append(canon_uid.data(), uid_len);
                    append_pod(buf, cid_len);
                    buf.append(cid.data(), cid_len);
                    append_pod(buf, ts);
                    append_pod(buf, camp_idx);
                    if (buf.size() >= 60000) flush_bucket(ub);
                }
            }
            for (int ub = 0; ub < NUM_BUCKETS; ++ub) flush_bucket(ub);
        };

        std::vector<std::thread> threads;
        for (int t = 0; t < ncpu; ++t) threads.emplace_back(worker);
        for (auto& th : threads) th.join();
        user_cl_writers.close_all();
    }

    // Free links memory before Phase 4
    {
        LinkResolver empty_links;
        std::swap(links, empty_links);
    }

    // 8. Phase 4: Process each user bucket in parallel -> sessionize, attribute, assists, aggregate
    struct EvRec {
        int64_t ts;
        uint32_t price_cents;
        uint16_t cat_id;
        uint8_t is_purchase;
    };
    struct ClRec {
        int64_t ts;
        uint32_t camp_idx;
        std::string_view cid;
    };

    std::vector<std::unordered_map<CampDayKey, CampStats, CampDayHash>> thread_camp_maps(ncpu);
    std::atomic<int> next_bucket{0};

    // Output binary arrays for user_daily (protected by a mutex for chunked flush)
    std::mutex ud_mutex;
    FILE* f_ud_uid_data = std::fopen((scratch_dir / "ud_uid_data.bin").string().c_str(), "wb");
    FILE* f_ud_uid_off  = std::fopen((scratch_dir / "ud_uid_off.bin").string().c_str(), "wb");
    FILE* f_ud_day      = std::fopen((scratch_dir / "ud_day.bin").string().c_str(), "wb");
    FILE* f_ud_sess     = std::fopen((scratch_dir / "ud_sess.bin").string().c_str(), "wb");
    FILE* f_ud_ev       = std::fopen((scratch_dir / "ud_ev.bin").string().c_str(), "wb");
    FILE* f_ud_rev      = std::fopen((scratch_dir / "ud_rev.bin").string().c_str(), "wb");
    FILE* f_ud_cat      = std::fopen((scratch_dir / "ud_cat.bin").string().c_str(), "wb");
    int64_t global_uid_offset = 0;
    std::fwrite(&global_uid_offset, sizeof(int64_t), 1, f_ud_uid_off);
    int64_t total_ud_rows = 0;

    auto phase4_worker = [&](int tid) {
        auto& camp_map = thread_camp_maps[tid];
        std::vector<uint32_t> camp_count(num_campaigns, 0);
        std::vector<uint32_t> active_camps;
        active_camps.reserve(256);

        // Local buffers for user_daily output
        std::string l_uid_data;
        std::vector<uint32_t> l_uid_lens;
        std::vector<int32_t> l_day;
        std::vector<int64_t> l_sess;
        std::vector<int64_t> l_ev;
        std::vector<int64_t> l_rev;
        std::vector<int32_t> l_cat;

        auto flush_ud = [&]() {
            if (l_day.empty()) return;
            std::lock_guard<std::mutex> lk(ud_mutex);
            std::fwrite(l_uid_data.data(), 1, l_uid_data.size(), f_ud_uid_data);
            std::vector<int64_t> offs(l_uid_lens.size());
            for (size_t i = 0; i < l_uid_lens.size(); ++i) {
                global_uid_offset += l_uid_lens[i];
                offs[i] = global_uid_offset;
            }
            std::fwrite(offs.data(), sizeof(int64_t), offs.size(), f_ud_uid_off);
            std::fwrite(l_day.data(), sizeof(int32_t), l_day.size(), f_ud_day);
            std::fwrite(l_sess.data(), sizeof(int64_t), l_sess.size(), f_ud_sess);
            std::fwrite(l_ev.data(), sizeof(int64_t), l_ev.size(), f_ud_ev);
            std::fwrite(l_rev.data(), sizeof(int64_t), l_rev.size(), f_ud_rev);
            std::fwrite(l_cat.data(), sizeof(int32_t), l_cat.size(), f_ud_cat);
            total_ud_rows += static_cast<int64_t>(l_day.size());

            l_uid_data.clear();
            l_uid_lens.clear();
            l_day.clear();
            l_sess.clear();
            l_ev.clear();
            l_rev.clear();
            l_cat.clear();
        };

        std::vector<int64_t> day_cat_rev(cat_names.size(), 0);
        std::vector<uint16_t> touched_cats;

        while (true) {
            int b = next_bucket.fetch_add(1);
            if (b >= NUM_BUCKETS) break;

            std::string ev_path = (scratch_dir / ("user_ev_" + std::to_string(b) + ".bin")).string();
            std::string cl_path = (scratch_dir / ("user_cl_" + std::to_string(b) + ".bin")).string();

            // Load events for this bucket
            std::string ev_raw;
            {
                std::ifstream in(ev_path, std::ios::binary | std::ios::ate);
                if (in) {
                    size_t sz = static_cast<size_t>(in.tellg());
                    ev_raw.resize(sz);
                    in.seekg(0);
                    in.read(ev_raw.data(), sz);
                }
                fs::remove(ev_path);
            }
            if (ev_raw.empty()) {
                fs::remove(cl_path);
                continue;
            }

            std::unordered_map<std::string_view, std::vector<EvRec>> user_evs;
            {
                const char* p = ev_raw.data();
                const char* end = ev_raw.data() + ev_raw.size();
                while (p < end) {
                    uint32_t uid_len = 0;
                    if (!read_pod(p, end, uid_len)) break;
                    std::string_view uid(p, uid_len);
                    p += uid_len;
                    EvRec r{};
                    read_pod(p, end, r.ts);
                    read_pod(p, end, r.price_cents);
                    read_pod(p, end, r.cat_id);
                    read_pod(p, end, r.is_purchase);
                    user_evs[uid].push_back(r);
                }
            }

            // Load clicks for this bucket (only for users that have events, and dedup on click_id)
            std::string cl_raw;
            {
                std::ifstream in(cl_path, std::ios::binary | std::ios::ate);
                if (in) {
                    size_t sz = static_cast<size_t>(in.tellg());
                    cl_raw.resize(sz);
                    in.seekg(0);
                    in.read(cl_raw.data(), sz);
                }
                fs::remove(cl_path);
            }

            std::unordered_map<std::string_view, std::vector<ClRec>> user_cls;
            if (!cl_raw.empty()) {
                std::unordered_set<std::string_view> seen_cids;
                seen_cids.reserve(cl_raw.size() / 40 + 256);
                const char* p = cl_raw.data();
                const char* end = cl_raw.data() + cl_raw.size();
                while (p < end) {
                    uint32_t uid_len = 0;
                    if (!read_pod(p, end, uid_len)) break;
                    std::string_view uid(p, uid_len);
                    p += uid_len;
                    uint32_t cid_len = 0;
                    read_pod(p, end, cid_len);
                    std::string_view cid(p, cid_len);
                    p += cid_len;
                    int64_t ts = 0;
                    uint32_t camp_idx = 0;
                    read_pod(p, end, ts);
                    read_pod(p, end, camp_idx);

                    if (user_evs.find(uid) == user_evs.end()) continue;
                    if (!seen_cids.insert(cid).second) continue; // dedup click_id
                    user_cls[uid].push_back(ClRec{ts, camp_idx, cid});
                }
            }

            // Process each user
            for (auto& kv : user_evs) {
                std::string_view uid = kv.first;
                auto& evs = kv.second;
                std::sort(evs.begin(), evs.end(), [](const EvRec& a, const EvRec& b) {
                    return a.ts < b.ts;
                });

                std::vector<ClRec>* cls = nullptr;
                auto cl_it = user_cls.find(uid);
                if (cl_it != user_cls.end() && !cl_it->second.empty()) {
                    cls = &cl_it->second;
                    // Sort by (ts ASC, cid DESC) so cls[right - 1] is max ts, tie-broken by byte-wise smallest cid!
                    std::sort(cls->begin(), cls->end(), [](const ClRec& a, const ClRec& b) {
                        if (a.ts != b.ts) return a.ts < b.ts;
                        return a.cid > b.cid;
                    });
                }

                size_t cl_left = 0, cl_right = 0;
                const size_t n_cls = cls ? cls->size() : 0;

                // Walk sessions; since session_start is monotonically increasing, day is also monotonically non-decreasing!
                int32_t cur_day = 0;
                bool has_cur_day = false;
                int64_t ud_sess = 0, ud_ev = 0, ud_rev = 0;
                bool ud_has_purch = false;

                auto finish_user_day = [&]() {
                    if (!has_cur_day) return;
                    int32_t top_cat = -1;
                    if (ud_has_purch) {
                        int64_t best_rev = -1;
                        uint16_t best_cat = 0;
                        for (uint16_t c : touched_cats) {
                            int64_t r = day_cat_rev[c];
                            if (r > best_rev || (r == best_rev && c < best_cat)) {
                                best_rev = r;
                                best_cat = c;
                            }
                            day_cat_rev[c] = 0;
                        }
                        top_cat = static_cast<int32_t>(best_cat);
                    }
                    touched_cats.clear();

                    l_uid_data.append(uid.data(), uid.size());
                    l_uid_lens.push_back(static_cast<uint32_t>(uid.size()));
                    l_day.push_back(cur_day);
                    l_sess.push_back(ud_sess);
                    l_ev.push_back(ud_ev);
                    l_rev.push_back(ud_rev);
                    l_cat.push_back(top_cat);

                    if (l_day.size() >= 65536) flush_ud();
                    ud_sess = 0; ud_ev = 0; ud_rev = 0; ud_has_purch = false;
                };

                const size_t n_evs = evs.size();
                size_t i = 0;
                while (i < n_evs) {
                    int64_t sess_start = evs[i].ts;
                    int32_t day = static_cast<int32_t>(floor_div(sess_start, MS_PER_DAY));
                    if (!has_cur_day) {
                        cur_day = day;
                        has_cur_day = true;
                    } else if (day != cur_day) {
                        finish_user_day();
                        cur_day = day;
                    }

                    size_t j = i + 1;
                    while (j < n_evs && evs[j].ts - evs[j - 1].ts <= MS_30_MIN) {
                        ++j;
                    }

                    int64_t s_events = static_cast<int64_t>(j - i);
                    int64_t s_rev = 0;
                    bool s_purch = false;
                    for (size_t k = i; k < j; ++k) {
                        if (evs[k].is_purchase) {
                            s_purch = true;
                            s_rev += evs[k].price_cents;
                            uint16_t c = evs[k].cat_id;
                            if (day_cat_rev[c] == 0) touched_cats.push_back(c);
                            day_cat_rev[c] += evs[k].price_cents;
                        }
                    }

                    ud_sess += 1;
                    ud_ev += s_events;
                    ud_rev += s_rev;
                    if (s_purch) ud_has_purch = true;

                    // Attribution & assists via sliding window on cls
                    uint32_t credited_camp = 0; // 0 = organic
                    if (cls) {
                        int64_t win_lo = sess_start - MS_7_DAYS;
                        while (cl_right < n_cls && (*cls)[cl_right].ts <= sess_start) {
                            uint32_t c = (*cls)[cl_right].camp_idx;
                            if (++camp_count[c] == 1) active_camps.push_back(c);
                            ++cl_right;
                        }
                        while (cl_left < cl_right && (*cls)[cl_left].ts < win_lo) {
                            uint32_t c = (*cls)[cl_left].camp_idx;
                            --camp_count[c];
                            ++cl_left;
                        }
                        if (cl_left < cl_right) {
                            credited_camp = (*cls)[cl_right - 1].camp_idx;
                            // Compact active_camps & record assists
                            size_t w = 0;
                            for (size_t idx = 0; idx < active_camps.size(); ++idx) {
                                uint32_t c = active_camps[idx];
                                if (camp_count[c] > 0) {
                                    active_camps[w++] = c;
                                    camp_map[CampDayKey{c, day}].assisted_sessions += 1;
                                }
                            }
                            active_camps.resize(w);
                        }
                    }

                    auto& cs = camp_map[CampDayKey{credited_camp, day}];
                    cs.sessions += 1;
                    if (s_purch) cs.purchasing_sessions += 1;
                    cs.revenue_cents += s_rev;

                    i = j;
                }

                finish_user_day();

                // Clean up camp_count for next user
                for (uint32_t c : active_camps) camp_count[c] = 0;
                active_camps.clear();
            }
        }
        flush_ud();
    };

    {
        std::vector<std::thread> threads;
        for (int t = 0; t < ncpu; ++t) threads.emplace_back(phase4_worker, t);
        for (auto& th : threads) th.join();
    }

    std::fclose(f_ud_uid_data);
    std::fclose(f_ud_uid_off);
    std::fclose(f_ud_day);
    std::fclose(f_ud_sess);
    std::fclose(f_ud_ev);
    std::fclose(f_ud_rev);
    std::fclose(f_ud_cat);

    // Write category lookup table for Python
    {
        FILE* f_cats = std::fopen((scratch_dir / "categories.bin").string().c_str(), "wb");
        uint32_t nc = static_cast<uint32_t>(cat_names.size());
        std::fwrite(&nc, sizeof(uint32_t), 1, f_cats);
        for (const auto& s : cat_names) {
            uint32_t l = static_cast<uint32_t>(s.size());
            std::fwrite(&l, sizeof(uint32_t), 1, f_cats);
            std::fwrite(s.data(), 1, l, f_cats);
        }
        std::fclose(f_cats);
    }

    // Merge campaign_daily maps and write flat binary files
    std::unordered_map<CampDayKey, CampStats, CampDayHash> final_camp;
    for (const auto& m : thread_camp_maps) {
        for (const auto& kv : m) {
            auto& dst = final_camp[kv.first];
            dst.sessions += kv.second.sessions;
            dst.purchasing_sessions += kv.second.purchasing_sessions;
            dst.revenue_cents += kv.second.revenue_cents;
            dst.assisted_sessions += kv.second.assisted_sessions;
        }
    }

    {
        FILE* f_cd_cid_data = std::fopen((scratch_dir / "cd_cid_data.bin").string().c_str(), "wb");
        FILE* f_cd_cid_off  = std::fopen((scratch_dir / "cd_cid_off.bin").string().c_str(), "wb");
        FILE* f_cd_ch_data  = std::fopen((scratch_dir / "cd_ch_data.bin").string().c_str(), "wb");
        FILE* f_cd_ch_off   = std::fopen((scratch_dir / "cd_ch_off.bin").string().c_str(), "wb");
        FILE* f_cd_day      = std::fopen((scratch_dir / "cd_day.bin").string().c_str(), "wb");
        FILE* f_cd_sess     = std::fopen((scratch_dir / "cd_sess.bin").string().c_str(), "wb");
        FILE* f_cd_psess    = std::fopen((scratch_dir / "cd_psess.bin").string().c_str(), "wb");
        FILE* f_cd_rev      = std::fopen((scratch_dir / "cd_rev.bin").string().c_str(), "wb");
        FILE* f_cd_assist   = std::fopen((scratch_dir / "cd_assist.bin").string().c_str(), "wb");

        int64_t cid_off = 0, ch_off = 0;
        std::fwrite(&cid_off, sizeof(int64_t), 1, f_cd_cid_off);
        std::fwrite(&ch_off, sizeof(int64_t), 1, f_cd_ch_off);
        int64_t actual_cd_rows = 0;

        for (const auto& kv : final_camp) {
            const auto& k = kv.first;
            const auto& v = kv.second;
            if (v.sessions == 0 && v.assisted_sessions == 0) continue;
            const std::string& cid = camp_ids[k.camp_idx];
            const std::string& ch  = camp_channels[k.camp_idx];
            std::fwrite(cid.data(), 1, cid.size(), f_cd_cid_data);
            cid_off += static_cast<int64_t>(cid.size());
            std::fwrite(&cid_off, sizeof(int64_t), 1, f_cd_cid_off);

            std::fwrite(ch.data(), 1, ch.size(), f_cd_ch_data);
            ch_off += static_cast<int64_t>(ch.size());
            std::fwrite(&ch_off, sizeof(int64_t), 1, f_cd_ch_off);

            std::fwrite(&k.day, sizeof(int32_t), 1, f_cd_day);
            std::fwrite(&v.sessions, sizeof(int64_t), 1, f_cd_sess);
            std::fwrite(&v.purchasing_sessions, sizeof(int64_t), 1, f_cd_psess);
            std::fwrite(&v.revenue_cents, sizeof(int64_t), 1, f_cd_rev);
            std::fwrite(&v.assisted_sessions, sizeof(int64_t), 1, f_cd_assist);
            actual_cd_rows++;
        }

        std::fclose(f_cd_cid_data);
        std::fclose(f_cd_cid_off);
        std::fclose(f_cd_ch_data);
        std::fclose(f_cd_ch_off);
        std::fclose(f_cd_day);
        std::fclose(f_cd_sess);
        std::fclose(f_cd_psess);
        std::fclose(f_cd_rev);
        std::fclose(f_cd_assist);

        FILE* f_meta = std::fopen((scratch_dir / "meta.bin").string().c_str(), "wb");
        std::fwrite(&total_ud_rows, sizeof(int64_t), 1, f_meta);
        std::fwrite(&actual_cd_rows, sizeof(int64_t), 1, f_meta);
        std::fclose(f_meta);
    }

    return 0;
}