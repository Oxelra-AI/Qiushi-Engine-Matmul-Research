// Untrusted certificate producer. Lean must check the emitted transports.
// Input: number of representatives, then (dimension, basis codes) for each.
// Output: JSONL orbit sizes and distinct one-vector extension witnesses.
// --queries FILE instead checks explicitly listed subspace bases against the same orbits.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using Key = unsigned __int128;
using Basis = std::array<unsigned, 9>;

struct Hash {
    std::size_t operator()(Key k) const {
        std::uint64_t x = std::uint64_t(k) ^ (std::uint64_t(k >> 64) * 0x9e3779b97f4a7c15ULL);
        x ^= x >> 30;
        x *= 0xbf58476d1ce4e5b9ULL;
        x ^= x >> 27;
        x *= 0x94d049bb133111ebULL;
        return x ^ (x >> 31);
    }
};

void insert(Basis &basis, unsigned x) {
    if (x >= 512) throw std::runtime_error("matrix code outside nine bits");
    for (int p = 8; p >= 0; --p) {
        if (!(x & (1U << p))) continue;
        if (basis[p]) { x ^= basis[p]; continue; }
        for (int q = p - 1; q >= 0; --q)
            if (x & (1U << q)) x ^= basis[q];
        for (int q = p + 1; q < 9; ++q)
            if (basis[q] & (1U << p)) basis[q] ^= x;
        basis[p] = x;
        return;
    }
}

Key encode(const Basis &basis) {
    Key key = 0;
    for (int p = 8; p >= 0; --p) key = (key << 9) | basis[p];
    return key;
}

Basis decode(Key key) {
    Basis basis{};
    for (unsigned &x : basis) { x = unsigned(key & 511); key >>= 9; }
    return basis;
}

unsigned gen(unsigned g, unsigned a) {
    if (g == 0) return ((a >> 3) & 7) | ((a & 7) << 3) | (a & 448);
    if (g == 1) return (a & 7) | (((a >> 6) & 7) << 3) | (((a >> 3) & 7) << 6);
    if (g == 2) return a ^ ((a >> 3) & 7);
    unsigned b = 0;
    for (unsigned i = 0; i < 3; ++i)
        for (unsigned j = 0; j < 3; ++j)
            b |= ((a >> (3 * i + j)) & 1) << (3 * j + i);
    return b;
}

Key image(Key key, unsigned g, const std::array<std::array<unsigned, 512>, 4> &maps) {
    Basis basis{};
    for (unsigned x : decode(key)) if (x) insert(basis, maps[g][x]);
    return encode(basis);
}

struct Node {
    Key key;
    std::uint32_t parent;
    std::uint16_t representative;
    std::uint8_t generator;
};

std::array<unsigned, 512> coefficients(const std::vector<unsigned> &basis) {
    if (basis.size() > 9) throw std::runtime_error("oversized coefficient basis");
    std::array<unsigned, 512> result;
    result.fill(1024);
    std::vector<unsigned> values(1U << basis.size());
    result[0] = 0;
    for (unsigned mask = 1; mask < values.size(); ++mask) {
        unsigned bit = __builtin_ctz(mask);
        values[mask] = values[mask & (mask - 1)] ^ basis[bit];
        result[values[mask]] = mask;
    }
    return result;
}

std::vector<std::vector<unsigned>> read_bases(std::istream &input, unsigned limit) {
    unsigned count;
    if (!(input >> count) || count == 0 || count > limit)
        throw std::runtime_error("invalid basis count");
    std::vector<std::vector<unsigned>> raw(count);
    for (auto &rows : raw) {
        unsigned dim;
        if (!(input >> dim) || dim > 9) throw std::runtime_error("invalid dimension");
        Basis basis{};
        for (unsigned j = 0; j < dim; ++j) {
            unsigned code;
            if (!(input >> code)) throw std::runtime_error("truncated basis");
            rows.push_back(code);
            insert(basis, code);
        }
        if (unsigned(std::count_if(basis.begin(), basis.end(), [](unsigned x) { return x != 0; })) != dim)
            throw std::runtime_error("basis is not independent");
    }
    std::string extra;
    if (input >> extra) throw std::runtime_error("trailing input");
    return raw;
}

int main(int argc, char **argv) {
    try {
        if (argc != 1 && !(argc == 3 && std::string(argv[1]) == "--queries"))
            throw std::runtime_error("usage: producer [--queries FILE]");
        auto raw = read_bases(std::cin, 65535);
        unsigned count = unsigned(raw.size());
        std::vector<Basis> bases(count);
        for (unsigned i = 0; i < count; ++i)
            for (unsigned code : raw[i]) insert(bases[i], code);
        std::vector<std::vector<unsigned>> queries;
        if (argc == 3) {
            std::ifstream input(argv[2]);
            if (!input) throw std::runtime_error("cannot open query file");
            queries = read_bases(input, 1000000);
        }

        std::array<std::array<unsigned, 512>, 4> maps{};
        for (unsigned g = 0; g < 4; ++g) for (unsigned x = 0; x < 512; ++x) {
            maps[g][x] = gen(g, x);
            if (gen(g, maps[g][x]) != x) throw std::runtime_error("generator is not involutive");
        }
        std::vector<Node> nodes;
        nodes.reserve(8300000);
        std::unordered_map<Key, std::uint32_t, Hash> index;
        index.reserve(8300000);
        for (unsigned i = 0; i < count; ++i) {
            Key root = encode(bases[i]);
            auto [it, added] = index.emplace(root, nodes.size());
            if (!added) throw std::runtime_error("representatives share an orbit");
            auto first = std::uint32_t(nodes.size());
            nodes.push_back({root, first, std::uint16_t(i), 0});
            for (std::size_t cursor = first; cursor < nodes.size(); ++cursor) {
                Key source = nodes[cursor].key;
                for (unsigned g = 0; g < 4; ++g) {
                    Key target = image(source, g, maps);
                    auto [found, fresh] = index.emplace(target, nodes.size());
                    if (fresh) nodes.push_back({target, std::uint32_t(cursor), std::uint16_t(i), std::uint8_t(g)});
                    else if (nodes[found->second].representative != i)
                        throw std::runtime_error("orbit collision");
                }
            }
            std::cerr << "orbit " << i << " size " << nodes.size() - first
                      << " total " << nodes.size() << '\n';
            std::cout << "{\"orbit\":" << i << ",\"size\":" << nodes.size() - first << "}\n";
        }

        auto emit = [&](Key key, const std::vector<unsigned> &source, const std::string &identity) {
            auto found = index.find(key);
            if (found == index.end()) throw std::runtime_error("uncovered subspace");
            auto cursor = found->second;
            unsigned j = nodes[cursor].representative;
            std::vector<unsigned> word;
            while (nodes[cursor].parent != cursor) {
                word.push_back(nodes[cursor].generator);
                cursor = nodes[cursor].parent;
            }
            Key replay = encode(bases[j]);
            for (auto g = word.rbegin(); g != word.rend(); ++g) replay = image(replay, *g, maps);
            if (replay != key) throw std::runtime_error("transport replay mismatch");
            std::vector<unsigned> target = raw[j];
            for (unsigned &x : target)
                for (auto g = word.rbegin(); g != word.rend(); ++g) x = maps[*g][x];
            auto sourceMasks = coefficients(source);
            auto targetMasks = coefficients(target);
            std::cout << "{" << identity << ",\"target\":" << j << ",\"word\":[";
            for (unsigned k = 0; k < word.size(); ++k) std::cout << (k ? "," : "") << word[k];
            std::cout << "],\"forward\":[";
            for (unsigned k = 0; k < source.size(); ++k) {
                if (targetMasks[source[k]] == 1024) throw std::runtime_error("missing forward coefficient");
                std::cout << (k ? "," : "") << targetMasks[source[k]];
            }
            std::cout << "],\"backward\":[";
            for (unsigned k = 0; k < target.size(); ++k) {
                if (sourceMasks[target[k]] == 1024) throw std::runtime_error("missing backward coefficient");
                std::cout << (k ? "," : "") << sourceMasks[target[k]];
            }
            std::cout << "]}\n";
        };
        if (argc == 3) {
            for (unsigned i = 0; i < queries.size(); ++i) {
                Basis basis{};
                for (unsigned code : queries[i]) insert(basis, code);
                emit(encode(basis), queries[i], "\"query\":" + std::to_string(i));
            }
            std::cout << "{\"complete\":true,\"spaces\":" << nodes.size()
                      << ",\"queries\":" << queries.size() << "}\n";
            return 0;
        }
        std::size_t extensions = 0;
        for (unsigned i = 0; i < count; ++i) {
            std::unordered_set<Key, Hash> emitted;
            emitted.insert(encode(bases[i]));
            for (unsigned c = 0; c < 512; ++c) {
                Basis extended = bases[i];
                insert(extended, c);
                Key key = encode(extended);
                if (!emitted.insert(key).second) continue;
                std::vector<unsigned> source = raw[i];
                source.insert(source.begin(), c);
                emit(key, source, "\"source\":" + std::to_string(i) +
                     ",\"code\":" + std::to_string(c));
                ++extensions;
            }
        }
        std::cout << "{\"complete\":true,\"spaces\":" << nodes.size()
                  << ",\"extensions\":" << extensions << "}\n";
        return 0;
    } catch (const std::exception &e) {
        std::cerr << "FAILED: " << e.what() << '\n';
        return 1;
    }
}
