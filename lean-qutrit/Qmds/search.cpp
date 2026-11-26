// Test H(x) = 1 + N(x) + Tr(s*x^k + b*x^255) in GF(2^16).
// Splitting x into a norm-one direction and a nonzero GF(256) scalar
// makes it possible to check all normalized coefficients.
#include <array>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <vector>

using Element = uint16_t;
constexpr int order = 65535;
std::array<Element, order> powerOfTwo;
std::array<int, order+1> logarithm;

Element power(Element x, int e) {
    if (e == 0) return 1;
    if (x == 0) return 0;
    return powerOfTwo[(static_cast<int64_t>(logarithm[x]) * e) % order];
}
Element mul(Element a, Element b) {
    return a && b ? powerOfTwo[(logarithm[a]+logarithm[b])%order] : 0;
}
Element trace(Element x) { return x ^ power(x,256); }

int main() {
    // x^16+x^12+x^3+x+1. Check the whole multiplicative cycle.
    uint32_t v = 1;
    logarithm.fill(-1);
    for (int i=0; i<order; ++i) {
        if (v==0 || logarithm[v]!=-1) return 2;
        powerOfTwo[i]=v;
        logarithm[v]=i;
        v <<= 1;
        if (v & 65536) v ^= 0x1100b;
    }
    if (v!=1) return 2;
    std::vector<Element> base{0}, unit, coeffs;
    std::array<int,65536> index{};
    for (int i=0; i<255; ++i) {
        base.push_back(powerOfTwo[257*i]);
        index[base.back()]=i+1;
    }
    for (int i=0; i<257; ++i) unit.push_back(powerOfTwo[255*i]);
    for (int b=0; b<=order; ++b) if (trace(b)==1) coeffs.push_back(b);
    if (coeffs.size()!=256) return 2;
    // Translation by the constant is in GF(256); precompute the right hand sides.
    std::vector<std::array<int,257>> rhs(coeffs.size());
    for (size_t b=0; b<coeffs.size(); ++b)
        for (int a=0; a<257; ++a)
            rhs[b][a]=index[1 ^ trace(mul(coeffs[b],power(unit[a],255)))];
    int64_t tested=0;
    for (int k=1; k<255; ++k) {
        std::array<std::bitset<256>,256> image{};
        for (int A=0; A<256; ++A)
            for (int y=1; y<256; ++y)
                image[A].set(index[power(base[y],2) ^ mul(base[A],power(base[y],k))]);
        for (int s=1; s<256; ++s) {
            std::array<int,257> left{};
            for (int a=0; a<257; ++a)
                left[a]=index[mul(base[s], trace(power(unit[a],k)))];
            for (size_t b=0; b<coeffs.size(); ++b) {
                ++tested;
                int a=0;
                while (a<257 && !image[left[a]].test(rhs[b][a])) ++a;
                if (a==257) {
                    std::cout << "candidate k=" << k << " s=" << base[s]
                              << " b=" << coeffs[b] << '\n';
                    for (int t=0; t<=order; ++t)
                        if ((1 ^ power(t,257) ^ trace(mul(base[s],power(t,k))
                              ^ mul(coeffs[b],power(t,255))))==0) return 3;
                    std::cout << "all 65536 inputs checked\n";
                    return 0;
                }
            }
        }
    }
    std::cout << tested << " normalized candidates tested; each has a root\n";
}
