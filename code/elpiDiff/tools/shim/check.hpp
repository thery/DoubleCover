// Stand-in for cases/check.hpp: same Case API, a minimal dual number instead of
// autodiff, no dpllmad/catch2. Checks: tangent vs dual, adjoint vs dual (via
// <xbar, xdot> = <ybar, J xdot>), central finite differences, dot-product test.
#pragma once
#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <functional>
#include <random>
#include <span>
#include <string>
#include <vector>

namespace autodiff {
struct dual {
    double val = 0, grad = 0;
    dual() = default;
    dual(double v) : val(v) {}
    dual(double v, double g) : val(v), grad(g) {}
    dual& operator+=(const dual& b) { val += b.val; grad += b.grad; return *this; }
    dual& operator-=(const dual& b) { val -= b.val; grad -= b.grad; return *this; }
    dual& operator*=(const dual& b) { *this = dual(val * b.val, grad * b.val + val * b.grad); return *this; }
};
inline dual operator-(dual a) { return {-a.val, -a.grad}; }
inline dual operator+(dual a, dual b) { return {a.val + b.val, a.grad + b.grad}; }
inline dual operator-(dual a, dual b) { return {a.val - b.val, a.grad - b.grad}; }
inline dual operator*(dual a, dual b) { return {a.val * b.val, a.grad * b.val + a.val * b.grad}; }
inline dual operator/(dual a, dual b) { return {a.val / b.val, (a.grad * b.val - a.val * b.grad) / (b.val * b.val)}; }
#define CMP(op) inline bool operator op(dual a, dual b) { return a.val op b.val; }
CMP(<) CMP(<=) CMP(>) CMP(>=) CMP(==) CMP(!=)
#undef CMP
inline dual sin(dual a) { return {std::sin(a.val), std::cos(a.val) * a.grad}; }
inline dual cos(dual a) { return {std::cos(a.val), -std::sin(a.val) * a.grad}; }
inline dual exp(dual a) { return {std::exp(a.val), std::exp(a.val) * a.grad}; }
inline dual log(dual a) { return {std::log(a.val), a.grad / a.val}; }
inline dual sqrt(dual a) { double s = std::sqrt(a.val); return {s, a.grad / (2 * s)}; }
inline dual pow(dual a, int k) { return {std::pow(a.val, k), k == 0 ? 0.0 : k * std::pow(a.val, k - 1) * a.grad}; }
inline dual abs(dual a) { return a.val < 0 ? -a : a; }
inline dual fabs(dual a) { return abs(a); }
}

namespace adjudge::check {
using dual = autodiff::dual;
template <typename S> using Primal = std::function<void(std::span<const S>, std::span<S>)>;
using Linear = std::function<void(std::span<const double>, std::span<const double>, std::span<double>)>;
struct Case {
    std::string name; std::size_t n = 0, m = 0; bool positive = false;
    Primal<double> primal; Primal<dual> primal_dual; Linear tangent, adjoint;
};
std::vector<Case> cases();
template <std::size_t N, typename S>
std::array<std::remove_const_t<S>, N> array_of(std::span<S> s, std::size_t offset = 0)
{ std::array<std::remove_const_t<S>, N> a{}; std::copy_n(s.begin() + offset, N, a.begin()); return a; }
template <typename S, std::size_t N>
void write(std::span<S> s, const std::array<S, N>& a, std::size_t offset = 0) { std::copy_n(a.begin(), N, s.begin() + offset); }
template <std::size_t N>
void accumulate(std::span<double> s, const std::array<double, N>& a, std::size_t offset = 0) { for (std::size_t k = 0; k < N; ++k) s[offset + k] += a[k]; }
}

namespace shim {
using namespace adjudge::check;
inline std::vector<double> rnd(std::size_t n, std::mt19937& g, bool pos = false) {
    std::uniform_real_distribution<double> mag(0.5, 1.5); std::bernoulli_distribution neg(0.5);
    std::vector<double> v(n); for (double& e : v) e = (!pos && neg(g)) ? -mag(g) : mag(g); return v; }
inline double inner(std::span<const double> a, std::span<const double> b) { double s = 0; for (std::size_t k = 0; k < a.size(); ++k) s += a[k] * b[k]; return s; }
inline bool close(double a, double b, double tol) { return std::abs(a - b) <= tol * std::max({1.0, std::abs(a), std::abs(b)}); }
}

int main()
{
    using namespace shim;
    int checks = 0, fails = 0;
    auto report = [&](bool ok, const std::string& what, double a, double b) {
        ++checks; if (!ok) { ++fails; std::printf("  FAIL %s: %.17g vs %.17g\n", what.c_str(), a, b); } };
    for (const Case& c : cases()) {
        std::mt19937 g(2026);
        for (int p = 0; p < 5; ++p) {
            auto x = rnd(c.n, g, c.positive), xdot = rnd(c.n, g), ybar = rnd(c.m, g);
            std::string at = c.name + ", point " + std::to_string(p);
            std::vector<dual> xd(c.n), yd(c.m);
            for (std::size_t k = 0; k < c.n; ++k) xd[k] = dual(x[k], xdot[k]);
            c.primal_dual(xd, yd);
            std::vector<double> jv(c.m); for (std::size_t j = 0; j < c.m; ++j) jv[j] = yd[j].grad;
            std::vector<double> ydot(c.m); c.tangent(x, xdot, ydot);
            for (std::size_t j = 0; j < c.m; ++j) report(close(ydot[j], jv[j], 1e-12), at + " tangent vs dual", ydot[j], jv[j]);
            std::vector<double> xbar(c.n, 0.0); c.adjoint(x, ybar, xbar);
            double l = inner(xbar, xdot), r = inner(ybar, jv), t = inner(ybar, ydot);
            report(close(l, r, 1e-12), at + " adjoint vs dual", l, r);
            report(close(l, t, 1e-12), at + " dot-product", l, t);
            const double h = 1e-6; std::vector<double> xp(x), xm(x), yp(c.m), ym(c.m);
            for (std::size_t k = 0; k < c.n; ++k) { xp[k] += h * xdot[k]; xm[k] -= h * xdot[k]; }
            c.primal(xp, yp); c.primal(xm, ym);
            std::vector<double> fd(c.m); for (std::size_t j = 0; j < c.m; ++j) fd[j] = (yp[j] - ym[j]) / (2 * h);
            double f = inner(ybar, fd); report(close(l, f, 1e-6), at + " adjoint vs finite differences", l, f);
        }
    }
    std::printf("  %d checks, %d failures\n", checks, fails);
    return fails != 0;
}
