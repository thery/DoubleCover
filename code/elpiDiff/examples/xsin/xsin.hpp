#pragma once
#include <cmath>

namespace adjudge {

template <typename T>
T xsin(T x)
{
    using std::sin;
    return x * sin(x);
}

} // namespace adjudge
