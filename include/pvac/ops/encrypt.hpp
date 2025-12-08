#pragma once

#include <cstdint>
#include <cmath>
#include <vector>
#include <unordered_set>
#include <utility>

#include "../core/types.hpp"
#include "../crypto/lpn.hpp"
#include "../crypto/matrix.hpp"
#include "../core/ct_safe.hpp"

namespace pvac {

inline std::pair<int,int> plan_noise(const PubKey& pk, int depth_hint) {
    double budget = pk.prm.noise_entropy_bits +
                    pk.prm.depth_slope_bits * std::max(0, depth_hint);
    double per2 = 2.0 * std::log2((double)pk.prm.B);
    double per3 = 3.0 * std::log2((double)pk.prm.B);

    int z2 = std::max(0, (int)std::floor((budget * pk.prm.tuple2_fraction) / std::max(1e-6, per2)));
    int z3 = std::max(0, (int)std::floor((budget * (1.0 - pk.prm.tuple2_fraction)) / std::max(1e-6, per3)));

    if (z2 + z3 == 1) { z3 > 0 ? ++z3 : ++z2; }
    return {z2, z3};
}

inline double sigma_density(const PubKey& pk, const Cipher& C) {
    if (C.E.empty()) return 0.0;
    long double ones = 0, total = 0;
    for (const auto& e : C.E) {
        ones += e.s.popcnt();
        total += pk.prm.m_bits;
    }
    return (double)(ones / total);
}

inline void compact_edges(const PubKey& pk, Cipher& C) {
    int B = pk.prm.B;
    size_t L = C.L.size();

    struct Agg { bool have_p = false, have_m = false; Fp wp, wm; BitVec sp, sm; };
    std::vector<Agg> acc(L * B);

    for (const auto& e : C.E) {
        Agg& a = acc[(size_t)e.layer_id * B + e.idx];
        if (e.ch == SGN_P) {
            if (!a.have_p) { a.wp = fp_from_u64(0); a.sp = BitVec::make(pk.prm.m_bits); a.have_p = true; }
            a.wp = fp_add(a.wp, e.w);
            a.sp.xor_with(e.s);
        } else {
            if (!a.have_m) { a.wm = fp_from_u64(0); a.sm = BitVec::make(pk.prm.m_bits); a.have_m = true; }
            a.wm = fp_add(a.wm, e.w);
            a.sm.xor_with(e.s);
        }
    }

    auto nz = [](const Fp& w, const BitVec& s) { return ct::fp_is_nonzero(w) || s.popcnt() != 0; };

    std::vector<Edge> out;
    out.reserve(C.E.size());
    for (size_t lid = 0; lid < L; lid++) {
        for (int k = 0; k < B; k++) {
            Agg& a = acc[lid * (size_t)B + k];
            if (a.have_p && nz(a.wp, a.sp)) out.push_back({(uint32_t)lid, (uint16_t)k, SGN_P, a.wp, a.sp});
            if (a.have_m && nz(a.wm, a.sm)) out.push_back({(uint32_t)lid, (uint16_t)k, SGN_M, a.wm, a.sm});
        }
    }
    C.E.swap(out);
}

inline void compact_layers(Cipher& C) {
    const size_t L = C.L.size();
    if (L == 0) return;

    std::vector<uint8_t> used(L, 0);
    for (const auto& e : C.E) if (e.layer_id < L) used[e.layer_id] = 1;

    for (bool changed = true; changed; ) {
        changed = false;
        for (size_t lid = 0; lid < L; ++lid) {
            if (!used[lid] || C.L[lid].rule != RRule::PROD) continue;
            auto mark = [&](uint32_t p) { if (p < L && !used[p]) { used[p] = 1; changed = true; } };
            mark(C.L[lid].pa);
            mark(C.L[lid].pb);
        }
    }

    std::vector<uint32_t> remap(L, UINT32_MAX);
    std::vector<Layer> newL;
    newL.reserve(L);

    for (size_t lid = 0; lid < L; ++lid)
        if (used[lid]) { remap[lid] = (uint32_t)newL.size(); newL.push_back(C.L[lid]); }

    if (newL.size() == L) return;

    for (auto& Lr : newL)
        if (Lr.rule == RRule::PROD) { Lr.pa = remap[Lr.pa]; Lr.pb = remap[Lr.pb]; }
    for (auto& e : C.E) e.layer_id = remap[e.layer_id];

    C.L.swap(newL);
}

inline void guard_budget(const PubKey& pk, Cipher& C, const char* where) {
    if (C.E.size() > pk.prm.edge_budget) {
        if (g_dbg) std::cout << "[guard] " << where << ": " << C.E.size() << " -> compact\n";
        compact_edges(pk, C);
    }
}

// ndt
inline Fp prf_noise_delta(const PubKey& pk, const SecKey& sk,
                          const RSeed& base_seed, uint32_t group_id, uint8_t kind) {
    RSeed s2 = base_seed;
    s2.nonce.lo ^= 0x9e3779b97f4a7c15ull * (uint64_t)group_id ^ (uint64_t)kind;
    s2.nonce.hi ^= 0x94d049bb133111ebull * (uint64_t)group_id ^ ((uint64_t)kind << 32);
    s2.ztag     ^= 0x517cc1b727220a95ull * (uint64_t)group_id ^ ((uint64_t)kind << 48);
    return prf_R(pk, sk, s2);
}

inline int pick_unique_idx(int B, std::unordered_set<int>& used) {
    int x;
    do { x = (int)(csprng_u64() % (uint64_t)B); } while (used.count(x));
    used.insert(x);
    return x;
}

inline int pick_distinct_idx(int B, int exclude) {
    int x;
    do { x = (int)(csprng_u64() % (uint64_t)B); } while (x == exclude);
    return x;
}

inline int pick_distinct_idx2(int B, int ex1, int ex2) {
    int x;
    do { x = (int)(csprng_u64() % (uint64_t)B); } while (x == ex1 || x == ex2);
    return x;
}

inline Edge make_edge(uint32_t lid, uint16_t idx, uint8_t ch, Fp w,
                      const PubKey& pk, const RSeed& seed) {
    return {lid, idx, ch, w, sigma_from_H(pk, seed.ztag, seed.nonce, idx, ch, csprng_u64())};
}

inline Cipher enc_fp_depth(const PubKey& pk, const SecKey& sk, const Fp& v, int depth_hint) {
    Cipher C;

    Layer L;
    L.rule = RRule::BASE;
    L.seed.nonce = make_nonce128();
    L.seed.ztag = prg_layer_ztag(pk.canon_tag, L.seed.nonce);
    C.L.push_back(L);

    constexpr int S = 8;
    std::unordered_set<int> used;
    used.reserve(S * 2);

    std::vector<int> idx(S);
    std::vector<uint8_t> ch(S);
    std::vector<Fp> r(S);

    for (int j = 0; j < S; j++) {
        idx[j] = pick_unique_idx(pk.prm.B, used);
        ch[j] = csprng_u64() & 1;
    }

    Fp sum1 = fp_from_u64(0), sumg = fp_from_u64(0);
    for (int j = 0; j < S - 2; j++) {
        r[j] = rand_fp_nonzero();
        int s = sgn_val(ch[j]);
        sum1 = s > 0 ? fp_add(sum1, r[j]) : fp_sub(sum1, r[j]);
        Fp term = fp_mul(r[j], pk.powg_B[idx[j]]);
        sumg = s > 0 ? fp_add(sumg, term) : fp_sub(sumg, term);
    }

    int ia = idx[S-2], ib = idx[S-1];
    int sa = sgn_val(ch[S-2]), sb = sgn_val(ch[S-1]);
    Fp ga = pk.powg_B[ia], gb = pk.powg_B[ib];

    Fp V = fp_sub(v, sumg);
    Fp rhs = fp_sub(fp_neg(fp_mul(sum1, ga)), V);
    Fp rb = fp_mul(rhs, fp_inv(fp_sub(ga, gb)));
    if (sb < 0) rb = fp_neg(rb);

    Fp tmp = sb > 0 ? fp_sub(fp_neg(sum1), rb) : fp_add(fp_neg(sum1), rb);
    Fp ra = sa > 0 ? tmp : fp_neg(tmp);

    r[S-2] = ra;
    r[S-1] = rb;

    Fp R = prf_R(pk, sk, L.seed);

    for (int j = 0; j < S; j++)
        C.E.push_back(make_edge(0, idx[j], ch[j], fp_mul(r[j], R), pk, L.seed));

    auto [Z2, Z3] = plan_noise(pk, depth_hint);
    int total_groups = Z2 + Z3;
    Fp delta_acc = fp_from_u64(0);
    int group_id = 0;

    auto next_delta = [&](int groups_left, uint8_t kind) -> Fp {
        if (groups_left <= 1) return fp_neg(delta_acc);
        Fp d = prf_noise_delta(pk, sk, L.seed, group_id, kind);
        delta_acc = fp_add(delta_acc, d);
        return d;
    };

    for (int t = 0; t < Z2; ++t, ++group_id) {
        int i = csprng_u64() % pk.prm.B;
        int j = pick_distinct_idx(pk.prm.B, i);

        uint8_t s1 = csprng_u64() & 1, s2 = s1 ^ 1;
        int sign1 = sgn_val(s1);

        Fp Delta = next_delta(total_groups - group_id, 0);
        Fp Delta_prime = sign1 > 0 ? Delta : fp_neg(Delta);

        Fp gi = pk.powg_B[i], gj = pk.powg_B[j];
        Fp r_i = rand_fp_nonzero();
        Fp r_j = fp_mul(fp_sub(fp_mul(r_i, gi), Delta_prime), fp_inv(gj));

        C.E.push_back(make_edge(0, i, s1, fp_mul(r_i, R), pk, L.seed));
        C.E.push_back(make_edge(0, j, s2, fp_mul(r_j, R), pk, L.seed));
    }

    for (int t = 0; t < Z3; ++t, ++group_id) {
        int i = csprng_u64() % pk.prm.B;
        int j = pick_distinct_idx(pk.prm.B, i);
        int k = pick_distinct_idx2(pk.prm.B, i, j);

        uint8_t s1 = csprng_u64() & 1, s2 = csprng_u64() & 1, s3 = csprng_u64() & 1;
        int sign1 = sgn_val(s1), sign2 = sgn_val(s2), sign3 = sgn_val(s3);

        Fp Delta = next_delta(total_groups - group_id, 1);
        Fp a = rand_fp_nonzero(), b = rand_fp_nonzero();

        Fp term1 = fp_mul(a, pk.powg_B[i]);
        Fp term2 = fp_mul(b, pk.powg_B[j]);
        if (sign1 < 0) term1 = fp_neg(term1);
        if (sign2 < 0) term2 = fp_neg(term2);

        Fp gk_signed = sign3 > 0 ? pk.powg_B[k] : fp_neg(pk.powg_B[k]);
        Fp c = fp_mul(fp_sub(Delta, fp_add(term1, term2)), fp_inv(gk_signed));

        C.E.push_back(make_edge(0, i, s1, fp_mul(a, R), pk, L.seed));
        C.E.push_back(make_edge(0, j, s2, fp_mul(b, R), pk, L.seed));
        C.E.push_back(make_edge(0, k, s3, fp_mul(c, R), pk, L.seed));
    }

    guard_budget(pk, C, "enc");
    return C;
}

inline Cipher combine_ciphers(const PubKey& pk, const Cipher& a, const Cipher& b) {
    Cipher C;
    C.L.reserve(a.L.size() + b.L.size());
    C.E.reserve(a.E.size() + b.E.size());

    for (const auto& L : a.L) C.L.push_back(L);
    uint32_t off = (uint32_t)a.L.size();

    for (auto L : b.L) {
        if (L.rule == RRule::PROD) { L.pa += off; L.pb += off; }
        C.L.push_back(L);
    }

    for (const auto& e : a.E) C.E.push_back(e);
    for (auto e : b.E) { e.layer_id += off; C.E.push_back(std::move(e)); }

    guard_budget(pk, C, "combine");
    compact_layers(C);
    return C;
}

inline Cipher enc_value_depth(const PubKey& pk, const SecKey& sk, uint64_t v, int depth_hint) {
    Fp val = fp_from_u64(v);
    Fp mask = rand_fp_nonzero();
    return combine_ciphers(pk,
        enc_fp_depth(pk, sk, fp_add(val, mask), depth_hint),
        enc_fp_depth(pk, sk, fp_neg(mask), depth_hint));
}

inline Cipher enc_value(const PubKey& pk, const SecKey& sk, uint64_t v) {
    return enc_value_depth(pk, sk, v, 0);
}

inline Cipher enc_zero_depth(const PubKey& pk, const SecKey& sk, int depth_hint) {
    Fp mask = rand_fp_nonzero();
    return combine_ciphers(pk,
        enc_fp_depth(pk, sk, mask, depth_hint),
        enc_fp_depth(pk, sk, fp_neg(mask), depth_hint));
}

}
