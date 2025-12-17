#include <pvac/pvac.hpp>
#include <pvac/utils/text.hpp>
#include <iostream>
#include <vector>
#include <fstream>
#include <filesystem>
#include <unordered_map>
#include <unordered_set>
#include <iomanip>

using namespace pvac;
namespace fs = std::filesystem;

// --- COPY DARI bounty2_test.cpp ---
namespace Magic {
    constexpr uint32_t CT = 0x66699666;
    constexpr uint32_t PK = 0x06660666;
    constexpr uint32_t VER = 1;
}

namespace io {
    auto put32 = [](std::ostream& o, uint32_t x) -> std::ostream& {
        return o.write(reinterpret_cast<const char*>(&x), 4);
    };
    auto put64 = [](std::ostream& o, uint64_t x) -> std::ostream& {
        return o.write(reinterpret_cast<const char*>(&x), 8);
    };
    auto get32 = [](std::istream& i) -> uint32_t {
        uint32_t x = 0; i.read(reinterpret_cast<char*>(&x), 4); return x;
    };
    auto get64 = [](std::istream& i) -> uint64_t {
        uint64_t x = 0; i.read(reinterpret_cast<char*>(&x), 8); return x;
    };
    auto putBv = [](std::ostream& o, const BitVec& b) -> std::ostream& {
        put32(o, (uint32_t)b.nbits);
        for (size_t i = 0; i < (b.nbits + 63) / 64; ++i) put64(o, b.w[i]);
        return o;
    };
    auto getBv = [](std::istream& i) -> BitVec {
        auto b = BitVec::make((int)get32(i));
        for (size_t j = 0; j < (b.nbits + 63) / 64; ++j) b.w[j] = get64(i);
        return b;
    };
    auto putFp = [](std::ostream& o, const Fp& f) -> std::ostream& {
        put64(o, f.lo); return put64(o, f.hi);
    };
    auto getFp = [](std::istream& i) -> Fp {
        return {get64(i), get64(i)};
    };
}

namespace ser {
    using namespace io;
    auto getLayer = [](std::istream& i) -> Layer {
        Layer L{};
        L.rule = (RRule)i.get();
        if (L.rule == RRule::BASE) {
            L.seed.ztag = get64(i);
            L.seed.nonce.lo = get64(i);
            L.seed.nonce.hi = get64(i);
        } else if (L.rule == RRule::PROD) {
            L.pa = get32(i);
            L.pb = get32(i);
        } else {
            (void)get64(i); (void)get64(i); (void)get64(i);
        }
        return L;
    };
    auto getEdge = [](std::istream& i) -> Edge {
        Edge e{};
        e.layer_id = get32(i);
        i.read(reinterpret_cast<char*>(&e.idx), 2);
        e.ch = (uint8_t)i.get();
        i.get();
        e.w = getFp(i);
        e.s = getBv(i);
        return e;
    };
    auto getCipher = [](std::istream& i) -> Cipher {
        Cipher C;
        auto nL = get32(i), nE = get32(i);
        C.L.resize(nL); C.E.resize(nE);
        for (auto& L : C.L) L = getLayer(i);
        for (auto& e : C.E) e = getEdge(i);
        return C;
    };
}

auto loadCts = [](const std::string& path) -> std::vector<Cipher> {
    std::ifstream i(path, std::ios::binary);
    if (!i || io::get32(i) != Magic::CT || io::get32(i) != Magic::VER)
        throw std::runtime_error("bad CT: " + path);
    std::vector<Cipher> cts(io::get64(i));
    for (auto& c : cts) c = ser::getCipher(i);
    return cts;
};

auto loadPk = [](const std::string& path) -> PubKey {
    std::ifstream i(path, std::ios::binary);
    if (!i || io::get32(i) != Magic::PK || io::get32(i) != Magic::VER)
        throw std::runtime_error("bad PK: " + path);
    PubKey pk;
    pk.prm.m_bits = io::get32(i);
    pk.prm.B = io::get32(i);
    pk.prm.lpn_t = io::get32(i);
    pk.prm.lpn_n = io::get32(i);
    pk.prm.lpn_tau_num = io::get32(i);
    pk.prm.lpn_tau_den = io::get32(i);
    pk.prm.noise_entropy_bits = io::get32(i);
    pk.prm.depth_slope_bits = io::get32(i);
    uint64_t t2 = io::get64(i);
    std::memcpy(&pk.prm.tuple2_fraction, &t2, 8);
    pk.prm.edge_budget = io::get32(i);
    pk.canon_tag = io::get64(i);
    i.read(reinterpret_cast<char*>(pk.H_digest.data()), 32);
    pk.H.resize(io::get64(i));
    for (auto& h : pk.H) h = io::getBv(i);
    pk.ubk.perm.resize(io::get64(i));
    for (auto& v : pk.ubk.perm) v = io::get32(i);
    pk.ubk.inv.resize(io::get64(i));
    for (auto& v : pk.ubk.inv) v = io::get32(i);
    pk.omega_B = io::getFp(i);
    pk.powg_B.resize(io::get64(i));
    for (auto& f : pk.powg_B) f = io::getFp(i);
    return pk;
};

// --- FUNGSI UTILITY ---
void print_hex(const std::string& label, const Fp& f) {
    std::cout << "  " << label << ": " 
              << std::hex << std::setw(16) << std::setfill('0') << f.hi
              << std::hex << std::setw(16) << std::setfill('0') << f.lo
              << std::dec << "\n";
}

// --- FUNGSI SERANGAN R² ---
Fp extract_R_squared(const PubKey& pk, const Cipher& ct, bool debug = false) {
    std::vector<size_t> layer0_edges;
    for (size_t i = 0; i < ct.E.size(); ++i) {
        if (ct.E[i].layer_id == 0) layer0_edges.push_back(i);
    }
    
    if (debug) std::cout << "  Found " << layer0_edges.size() << " edges in layer 0\n";

    for (size_t i = 0; i < layer0_edges.size(); ++i) {
        for (size_t j = i + 1; j < layer0_edges.size(); ++j) {
            const Edge& e1 = ct.E[layer0_edges[i]];
            const Edge& e2 = ct.E[layer0_edges[j]];
            
            if (e1.ch == e2.ch) continue;
            
            Fp g1 = pk.powg_B[e1.idx];
            Fp g2 = pk.powg_B[e2.idx];
            
            int s1 = sgn_val(e1.ch);
            int s2 = sgn_val(e2.ch);
            
            Fp t1 = fp_mul(e1.w, g1);
            if (s1 < 0) t1 = fp_neg(t1);
            
            Fp t2 = fp_mul(e2.w, g2);
            if (s2 < 0) t2 = fp_neg(t2);
            
            Fp cand = fp_add(t1, t2);
            Fp cand_neg = fp_neg(cand);
            
            if (debug) {
                std::cout << "    Pair (" << i << "," << j << "): idx=" 
                          << e1.idx << "," << e2.idx << " ch=" 
                          << (int)e1.ch << "," << (int)e2.ch << "\n";
                print_hex("    cand", cand);
                print_hex("    -cand", cand_neg);
            }
            
            return (cand.lo & 1) ? fp_neg(cand) : cand;
        }
    }
    return fp_from_u64(0);
}

// --- ANALISIS PERBANDINGAN CIPHERTEXT ---
void compare_ciphertexts(const PubKey& pk, const Cipher& ct1, const Cipher& ct2, 
                         const std::string& name1, const std::string& name2) {
    std::cout << "\n=== PERBANDINGAN " << name1 << " vs " << name2 << " ===\n";
    
    // 1. Bandingkan jumlah edge
    std::cout << "Jumlah edge:\n";
    std::cout << "  " << name1 << ": " << ct1.E.size() << "\n";
    std::cout << "  " << name2 << ": " << ct2.E.size() << "\n";
    
    // 2. Bandingkan edge di layer 0
    std::vector<Edge> edges1, edges2;
    for (const auto& e : ct1.E) if (e.layer_id == 0) edges1.push_back(e);
    for (const auto& e : ct2.E) if (e.layer_id == 0) edges2.push_back(e);
    
    std::cout << "Edge di Layer 0:\n";
    std::cout << "  " << name1 << ": " << edges1.size() << " edges\n";
    std::cout << "  " << name2 << ": " << edges2.size() << " edges\n";
    
    // 3. Cari edge dengan idx yang sama
    std::cout << "\nEdge dengan idx yang sama:\n";
    std::cout << "Idx\tCh1\tCh2\tw1.lo\t\tw2.lo\t\tg^idx.lo\n";
    std::cout << "---\t---\t---\t---------------\t---------------\t---------------\n";
    
    for (const auto& e1 : edges1) {
        for (const auto& e2 : edges2) {
            if (e1.idx == e2.idx) {
                Fp g = pk.powg_B[e1.idx];
                std::cout << e1.idx << "\t" << (int)e1.ch << "\t" << (int)e2.ch << "\t"
                          << std::hex << e1.w.lo << "\t" << e2.w.lo << "\t" << g.lo << std::dec << "\n";
                
                // Hitung perbandingan w1/w2
                if (ct::fp_is_nonzero(e2.w)) {
                    Fp ratio = fp_mul(e1.w, fp_inv(e2.w));
                    std::cout << "        Ratio w1/w2: " << std::hex << ratio.lo << std::dec << "\n";
                }
            }
        }
    }
}

// --- HITUNG SUM UNTUK SEMUA EDGE LAYER 0 ---
Fp compute_weighted_sum(const PubKey& pk, const Cipher& ct) {
    Fp sum = fp_from_u64(0);
    
    for (const auto& e : ct.E) {
        if (e.layer_id == 0) {
            Fp g = pk.powg_B[e.idx];
            Fp term = fp_mul(e.w, g);
            int s = sgn_val(e.ch);
            
            if (s > 0) {
                sum = fp_add(sum, term);
            } else {
                sum = fp_sub(sum, term);
            }
        }
    }
    
    return sum;
}

// --- MAIN ---
int main() {
    std::cout << "=== BOUNTY 2 - ANALISIS DETAIL ===\n";
    std::cout << "Tujuan: Pecahkan ciphertext a.ct (nilai 1) dan b.ct (nilai 2)\n\n";
    
    try {
        // 1. Load data
        std::cout << "[1] Loading data...\n";
        const std::string dir = "bounty2_data";
        auto pk = loadPk(dir + "/pk.bin");
        auto cta_vec = loadCts(dir + "/a.ct");
        auto ctb_vec = loadCts(dir + "/b.ct");
        
        if (cta_vec.empty() || ctb_vec.empty()) {
            throw std::runtime_error("Failed to load ciphertexts");
        }
        
        const Cipher& ct_a = cta_vec[0];  // a = 1
        const Cipher& ct_b = ctb_vec[0];  // b = 2
        
        std::cout << "    ✓ Data loaded\n";
        std::cout << "    - pk.B = " << pk.prm.B << "\n";
        std::cout << "    - pk.powg_B size = " << pk.powg_B.size() << "\n";
        
        // 2. Ekstrak R² dengan debug
        std::cout << "\n[2] Mengekstrak R² dari ciphertext...\n";
        Fp R2_a = extract_R_squared(pk, ct_a, true);
        std::cout << "    R² untuk a.ct (nilai 1):\n";
        print_hex("      Nilai", R2_a);
        
        Fp R2_b = extract_R_squared(pk, ct_b, true);
        std::cout << "    R² untuk b.ct (nilai 2):\n";
        print_hex("      Nilai", R2_b);
        
        // 3. Hitung perbandingan R²
        std::cout << "\n[3] Analisis perbandingan R²:\n";
        if (ct::fp_is_nonzero(R2_b)) {
            Fp ratio_R2 = fp_mul(R2_a, fp_inv(R2_b));
            print_hex("    R²_a / R²_b", ratio_R2);
            
            // Coba tebak: jika a=1 dan b=2, apa hubungannya?
            // Mungkin R²_a / R²_b = (1/2)² = 0.25 atau hubungan lain
        }
        
        // 4. Hitung weighted sum untuk setiap ciphertext
        std::cout << "\n[4] Menghitung weighted sum Σ sgn* w * g^idx:\n";
        Fp sum_a = compute_weighted_sum(pk, ct_a);
        Fp sum_b = compute_weighted_sum(pk, ct_b);
        
        std::cout << "    Untuk a.ct (harusnya ≈ R * 1):\n";
        print_hex("      sum_a", sum_a);
        
        std::cout << "    Untuk b.ct (harusnya ≈ R * 2):\n";
        print_hex("      sum_b", sum_b);
        
        // 5. Cari hubungan antara sum dan R²
        std::cout << "\n[5] Mencari hubungan matematis:\n";
        if (ct::fp_is_nonzero(sum_b)) {
            Fp ratio_sum = fp_mul(sum_a, fp_inv(sum_b));
            print_hex("    sum_a / sum_b", ratio_sum);
            std::cout << "    (Harusnya mendekati 1/2 = 0.5 jika a=1 dan b=2)\n";
        }
        
        // 6. Bandingkan ciphertext secara langsung
        compare_ciphertexts(pk, ct_a, ct_b, "a.ct (nilai 1)", "b.ct (nilai 2)");
        
        // 7. Eksperimen: coba tebak R dari R²
        std::cout << "\n[6] Eksperimen pemulihan nilai:\n";
        std::cout << "    Jika sum_a = R * 1, maka R = sum_a\n";
        std::cout << "    Tapi kita punya R², bukan R...\n";
        
        // Coba hitung R dari sum_a (asumsi plaintext = 1)
        Fp R_guess_a = sum_a;  // Karena sum_a = R * 1
        Fp R2_guess_a = fp_mul(R_guess_a, R_guess_a);
        
        std::cout << "    Jika a=1, maka R_guess = sum_a:\n";
        print_hex("      R_guess", R_guess_a);
        print_hex("      R_guess²", R2_guess_a);
        print_hex("      R²_actual", R2_a);
        
        std::cout << "    Perbedaan R_guess² vs R²_actual:\n";
        Fp diff = fp_sub(R2_guess_a, R2_a);
        print_hex("      Selisih", diff);
        
        // 8. Kesimpulan
        std::cout << "\n[7] KESIMPULAN AWAL:\n";
        std::cout << "    - R² berhasil diekstrak dari kedua ciphertext\n";
        std::cout << "    - Weighted sum (sum_a, sum_b) = R * plaintext\n";
        std::cout << "    - Tantangan: butuh R untuk dapat plaintext dari sum\n";
        std::cout << "    - Kemungkinan: eksploitasi 'noise_entropy_bits: 120' \n";
        std::cout << "      membuat R² atau sum punya pola yang bisa ditebak\n";
        
        // 9. Saran langkah berikut
        std::cout << "\n[8] LANGKAH BERIKUTNYA:\n";
        std::cout << "    1. Analisis lebih dalam hubungan sum_a dan sum_b\n";
        std::cout << "    2. Cari pola di byte ciphertext a.ct vs b.ct\n";
        std::cout << "    3. Eksploitasi 'combine_ciphers' untuk operasi a+b\n";
        std::cout << "    4. Gunakan attack R² pada ciphertext hasil penjumlahan\n";
        
    } catch (const std::exception& e) {
        std::cerr << "\nERROR: " << e.what() << "\n";
        return 1;
    }
    
    std::cout << "\n=== ANALISIS SELESAI ===\n";
    return 0;
}
