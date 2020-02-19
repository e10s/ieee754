module ieee754.math;

import ieee754.type : Binary32, Binary64, isIEEE754Binary;

///
T fabs(T)(const(T) x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    return x.sign ? -x : x;
}

///
@safe pure nothrow @nogc unittest
{
    assert(isIdentical(fabs(Binary32.zero), Binary32.zero));
    assert(isIdentical(fabs(-Binary32.zero), Binary32.zero));
    assert(fabs(Binary32(-10.0)) == Binary32(10.0));
}

///
@safe pure nothrow @nogc unittest
{
    assert(isIdentical(fabs(Binary64.zero), Binary64.zero));
    assert(isIdentical(fabs(-Binary64.zero), Binary64.zero));
    assert(fabs(Binary64(-10.0)) == Binary64(10.0));
}

///
T sqrt(T)(const(T) x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    if (x.isNaN || x.isInfinity || x.isZero)
    {
        return x;
    }

    if (x.sign)
    {
        return -T.nan; // Why -???
    }

    import ieee754.core : Fixed;

    auto x2 = Fixed!T(x);

    if (x2.exponentUnbiased % 2)
    {
        x2.shiftMantissaToLeft(1);
    }

    assert(x2.integerPart);
    assert(x2.integerPart < 0b111);
    assert(x2.exponentUnbiased % 2 == 0);

    immutable sqrtExponent = x2.exponentUnbiased / 2;

    // [padding][integer: 2].[fraction: fractionBits][margin: fractionBits]
    static if (is(T == Binary32))
    {
        immutable operandMantissa = cast(ulong) x2.mantissa << Fixed!T.fractionBits;
    }
    else static if (is(T == Binary64))
    {
        import ieee754.core : Ucent;

        immutable operandMantissa = Ucent(0, x2.mantissa) << Fixed!T.fractionBits;
    }
    else
    {
        static assert(0);
    }
    // [padding][integer: 1].[fraction: fractionBits]
    Fixed!T.MantType sqrtMantissa;

    Fixed!T.MantType tempAdd, tempMulSub;

    foreach_reverse (i; 1 .. Fixed!T.fractionBits + 1)
    {
        static if (is(T == Binary32))
        {
            immutable twoBits = (operandMantissa >>> (i * 2)) & 0b11;
        }
        else static if (is(T == Binary64))
        {
            immutable twoBits = (operandMantissa >>> (i * 2)).low & 0b11;
        }
        else
        {
            static assert(0);
        }
        tempMulSub <<= 2;
        tempMulSub |= twoBits;

        immutable bit = !(((tempAdd << 1) | 1) > tempMulSub);

        sqrtMantissa <<= 1;
        sqrtMantissa |= bit;

        immutable temp = (tempAdd << 1) | bit;
        tempAdd = temp + bit;
        tempMulSub -= temp * bit;
    }

    sqrtMantissa <<= 1;
    sqrtMantissa |= cast(bool) tempMulSub;

    // [padding][integer: 1].[fraction: fractionBits]
    assert(sqrtMantissa >>> Fixed!T.fractionBits == 1);

    import ieee754.core : round;

    return round(Fixed!T(0, sqrtExponent, sqrtMantissa));
}

///
@safe pure nothrow @nogc unittest
{
    static import std.math;

    assert(sqrt(Binary32(2.0)) == Binary32(std.math.sqrt(2.0f)));
    assert(sqrt(Binary32(9.0)) == Binary32(std.math.sqrt(9.0f)));

    assert(isNaN(sqrt(Binary32(-1.0f))));

    assert(sqrt(-Binary32.zero) == -Binary32.zero);

    immutable small = Binary32.min_normal / Binary32(7.0);
    assert(sqrt(small) == Binary32(std.math.sqrt(small.value)));
}

///
@safe pure nothrow @nogc unittest
{
    static import std.math;

    assert(sqrt(Binary64(2.0)) == Binary64(std.math.sqrt(2.0)));
    assert(sqrt(Binary64(9.0)) == Binary64(std.math.sqrt(9.0)));

    assert(isNaN(sqrt(Binary64(-1.0))));

    assert(sqrt(-Binary64.zero) == -Binary64.zero);

    immutable small = Binary64.min_normal / Binary64(7.0);
    assert(sqrt(small) == Binary64(std.math.sqrt(small.value)));
}

//---------------------------

///
int cmp(T)(T x, T y) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    if (x.sign != y.sign)
    {
        return x.sign ? -1 : 1;
    }

    immutable xMagnitude = (cast(T.FractionType) x.exponent << T.fractionBits) | x.fraction;
    immutable yMagnitude = (cast(T.FractionType) y.exponent << T.fractionBits) | y.fraction;

    immutable diff = (xMagnitude > yMagnitude) - (xMagnitude < yMagnitude);

    return x.sign ? -diff : diff;
}

///
pure nothrow @nogc @safe unittest
{
    assert(cmp(-Binary32.infinity, -Binary32.max) < 0);
    assert(cmp(-Binary32.max, Binary32(-100.0)) < 0);
    assert(cmp(Binary32(-100.0), Binary32(-0.5)) < 0);
    assert(cmp(Binary32(-0.5), Binary32(0.0)) < 0);
    assert(cmp(Binary32(0.0), Binary32(0.5)) < 0);
    assert(cmp(Binary32(0.5), Binary32(100.0)) < 0);
    assert(cmp(Binary32(100.0), Binary32.max) < 0);
    assert(cmp(Binary32.max, Binary32.infinity) < 0);

    assert(cmp(Binary32(1.0), Binary32(1.0)) == 0);

    assert(cmp(Binary32(-0.0), Binary32(+0.0)) < 0);
    assert(cmp(Binary32(+0.0), Binary32(-0.0)) > 0);

    assert(cmp(-Binary32.nan, -Binary32.infinity) < 0);
    assert(cmp(Binary32.infinity, Binary32.nan) < 0);
    assert(cmp(-Binary32.nan, Binary32.nan) < 0);

    assert(cmp(NaN!Binary32(10), NaN!Binary32(20)) < 0);
    assert(cmp(-NaN!Binary32(20), -NaN!Binary32(10)) < 0);
}

///
pure nothrow @nogc @safe unittest
{
    assert(cmp(-Binary64.infinity, -Binary64.max) < 0);
    assert(cmp(-Binary64.max, Binary64(-100.0)) < 0);
    assert(cmp(Binary64(-100.0), Binary64(-0.5)) < 0);
    assert(cmp(Binary64(-0.5), Binary64(0.0)) < 0);
    assert(cmp(Binary64(0.0), Binary64(0.5)) < 0);
    assert(cmp(Binary64(0.5), Binary64(100.0)) < 0);
    assert(cmp(Binary64(100.0), Binary64.max) < 0);
    assert(cmp(Binary64.max, Binary64.infinity) < 0);

    assert(cmp(Binary64(1.0), Binary64(1.0)) == 0);

    assert(cmp(Binary64(-0.0), Binary64(+0.0)) < 0);
    assert(cmp(Binary64(+0.0), Binary64(-0.0)) > 0);

    assert(cmp(-Binary64.nan, -Binary64.infinity) < 0);
    assert(cmp(Binary64.infinity, Binary64.nan) < 0);
    assert(cmp(-Binary64.nan, Binary64.nan) < 0);

    assert(cmp(NaN!Binary64(10), NaN!Binary64(20)) < 0);
    assert(cmp(-NaN!Binary64(20), -NaN!Binary64(10)) < 0);
}

///
ulong getNaNPayload(T)(T x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    enum qNaNBit = T.FractionType(1) << (T.fractionBits - 1);
    enum payloadMask = qNaNBit - 1;

    return x.fraction & payloadMask;
}

///
pure nothrow @nogc @safe unittest
{
    auto a = NaN!Binary32(1_000_000);
    assert(isNaN(a));
    assert(getNaNPayload(a) == 1_000_000);
}

///
pure nothrow @nogc @safe unittest
{
    auto a = NaN!Binary64(1_000_000);
    assert(isNaN(a));
    assert(getNaNPayload(a) == 1_000_000);
}

///
T NaN(T)(ulong payload) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    enum qNaNBit = T.FractionType(1) << (T.fractionBits - 1);
    enum payloadMask = qNaNBit - 1;

    return T(0, T.max_exp + T.bias, qNaNBit | (payload & payloadMask));
}

///
pure nothrow @nogc @safe unittest
{
    auto a = NaN!Binary32(1_000_000);
    assert(isNaN(a));
    assert(getNaNPayload(a) == 1_000_000);
}

///
pure nothrow @nogc @safe unittest
{
    auto a = NaN!Binary64(1_000_000);
    assert(isNaN(a));
    assert(getNaNPayload(a) == 1_000_000);
}

///
T nextDown(T)(const(T) x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    if (x == T.infinity)
    {
        return T.max;
    }

    return x - ulp(x);
}

///
pure nothrow @nogc @safe unittest
{
    assert(isNaN(nextDown(Binary32.init)));

    assert(nextDown(Binary32.infinity) == Binary32.max);
    assert(nextDown(Binary32.zero) == -Binary32.min_normal * Binary32.epsilon);
    assert(nextDown(-Binary32.max) == -Binary32.infinity);
    assert(nextDown(-Binary32.infinity) == -Binary32.infinity);

    assert(nextDown(Binary32(1.0) + Binary32.epsilon) == Binary32(1.0));
}

///
pure nothrow @nogc @safe unittest
{
    assert(isNaN(nextDown(Binary64.init)));

    assert(nextDown(Binary64.infinity) == Binary64.max);
    assert(nextDown(Binary64.zero) == -Binary64.min_normal * Binary64.epsilon);
    assert(nextDown(-Binary64.max) == -Binary64.infinity);
    assert(nextDown(-Binary64.infinity) == -Binary64.infinity);

    assert(nextDown(Binary64(1.0) + Binary64.epsilon) == Binary64(1.0));
}

///
T nextUp(T)(const(T) x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    if (x == -T.infinity)
    {
        return -T.max;
    }

    return x + ulp(x);
}

///
pure nothrow @nogc @safe unittest
{
    assert(isNaN(nextUp(Binary32.init)));

    assert(nextUp(-Binary32.infinity) == -Binary32.max);
    assert(nextUp(-Binary32.zero) == Binary32.min_normal * Binary32.epsilon);
    assert(nextUp(Binary32.max) == Binary32.infinity);
    assert(nextUp(Binary32.infinity) == Binary32.infinity);

    assert(nextUp(Binary32(1.0)) == Binary32(1.0) + Binary32.epsilon);
}

///
pure nothrow @nogc @safe unittest
{
    assert(isNaN(nextUp(Binary64.init)));

    assert(nextUp(-Binary64.infinity) == -Binary64.max);
    assert(nextUp(-Binary64.zero) == Binary64.min_normal * Binary64.epsilon);
    assert(nextUp(Binary64.max) == Binary64.infinity);
    assert(nextUp(Binary64.infinity) == Binary64.infinity);

    assert(nextUp(Binary64(1.0)) == Binary64(1.0) + Binary64.epsilon);
}

///
T ulp(T)(T x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    if (isNaN(x))
    {
        return x;
    }

    if (isInfinity(x))
    {
        return T.infinity;
    }

    if (isZero(x) || isSubnormal(x))
    {
        return T(0, 0, 1);
    }

    return T(0, x.exponent, 0) * T.epsilon;
}

///
pure nothrow @nogc @safe unittest
{
    assert(isNaN(ulp(Binary32.nan)));
    assert(ulp(-Binary32.infinity) == Binary32.infinity);
    assert(ulp(Binary32.zero) == Binary32.min_normal * Binary32.epsilon);
    assert(ulp(-Binary32(1.0)) == Binary32.epsilon);
}

///
pure nothrow @nogc @safe unittest
{
    assert(isNaN(ulp(Binary32.nan)));
    assert(ulp(-Binary32.infinity) == Binary32.infinity);
    assert(ulp(Binary32.zero) == Binary32.min_normal * Binary32.epsilon);
    assert(ulp(-Binary32(1.0)) == Binary32.epsilon);
}

//---------------------------

///
bool isFinite(T)(T x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    return x.exponent != T.max_exp + T.bias;
}

///
@safe pure nothrow @nogc unittest
{
    assert(isFinite(Binary32(1.23)));
    assert(isFinite(Binary32.max));
    assert(isFinite(Binary32.min_normal));
    assert(!isFinite(Binary32.nan));
    assert(!isFinite(Binary32.infinity));
}

///
@safe pure nothrow @nogc unittest
{
    assert(isFinite(Binary64(1.23)));
    assert(isFinite(Binary64.max));
    assert(isFinite(Binary64.min_normal));
    assert(!isFinite(Binary64.nan));
    assert(!isFinite(Binary64.infinity));
}

///
bool isIdentical(T)(T x, T y) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    return x.sign == y.sign && x.exponent == y.exponent && x.exponent == y.exponent;
}

///
@safe pure nothrow @nogc unittest
{
    assert(isIdentical(Binary32.zero, Binary32.zero));
    assert(isIdentical(Binary32(1.0), Binary32(1.0)));
    assert(isIdentical(Binary32.infinity, Binary32.infinity));
    assert(isIdentical(-Binary32.infinity, -Binary32.infinity));
    assert(!isIdentical(Binary32.zero, -Binary32.zero));
    assert(!isIdentical(Binary32.nan, -Binary32.nan));
    assert(!isIdentical(Binary32.infinity, -Binary32.infinity));
}

///
@safe pure nothrow @nogc unittest
{
    assert(isIdentical(Binary64.zero, Binary64.zero));
    assert(isIdentical(Binary64(1.0), Binary64(1.0)));
    assert(isIdentical(Binary64.infinity, Binary64.infinity));
    assert(isIdentical(-Binary64.infinity, -Binary64.infinity));
    assert(!isIdentical(Binary64.zero, -Binary64.zero));
    assert(!isIdentical(Binary64.nan, -Binary64.nan));
    assert(!isIdentical(Binary64.infinity, -Binary64.infinity));
}

///
bool isInfinity(T)(T x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    return x.exponent == T.max_exp + T.bias && !x.fraction;
}

///
@safe pure nothrow @nogc unittest
{
    assert(!isInfinity(Binary32.init));
    assert(!isInfinity(-Binary32.init));
    assert(!isInfinity(Binary32.nan));
    assert(!isInfinity(-Binary32.nan));
    assert(isInfinity(Binary32.infinity));
    assert(isInfinity(-Binary32.infinity));
    assert(isInfinity(-Binary32(1.0) / Binary32.zero));
}

///
@safe pure nothrow @nogc unittest
{
    assert(!isInfinity(Binary64.init));
    assert(!isInfinity(-Binary64.init));
    assert(!isInfinity(Binary64.nan));
    assert(!isInfinity(-Binary64.nan));
    assert(isInfinity(Binary64.infinity));
    assert(isInfinity(-Binary64.infinity));
    assert(isInfinity(-Binary64(1.0) / Binary64.zero));
}

///
bool isNaN(T)(T x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    return x.exponent == T.max_exp + T.bias && x.fraction;
}

///
@safe pure nothrow @nogc unittest
{
    assert(isNaN(Binary32.init));
    assert(isNaN(-Binary32.init));
    assert(isNaN(Binary32.nan));
    assert(isNaN(-Binary32.nan));
    assert(!isNaN(Binary32(53.6)));
    assert(!isNaN(Binary32(-53.6)));
}

///
@safe pure nothrow @nogc unittest
{
    assert(isNaN(Binary64.init));
    assert(isNaN(-Binary64.init));
    assert(isNaN(Binary64.nan));
    assert(isNaN(-Binary64.nan));
    assert(!isNaN(Binary64(53.6)));
    assert(!isNaN(Binary64(-53.6)));
}

///
bool isNormal(T)(T x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    return x.exponent && x.exponent != T.max_exp + T.bias;
}

///
@safe pure nothrow @nogc unittest
{
    immutable f = Binary32(3);
    immutable d = Binary32(500);
    immutable e = Binary32(10e+35);
    assert(isNormal(f));
    assert(isNormal(d));
    assert(isNormal(e));

    assert(!isNormal(Binary32.zero));
    assert(!isNormal(Binary32.infinity));
    assert(isNormal(-Binary32.max));
    assert(!isNormal(Binary32.min_normal / Binary32(4)));
}

///
@safe pure nothrow @nogc unittest
{
    immutable f = Binary64(3);
    immutable d = Binary64(500);
    immutable e = Binary64(10e+35);
    assert(isNormal(f));
    assert(isNormal(d));
    assert(isNormal(e));

    assert(!isNormal(Binary64.zero));
    assert(!isNormal(Binary64.infinity));
    assert(isNormal(-Binary64.max));
    assert(!isNormal(Binary64.min_normal / Binary64(4)));
}

///
bool isPowerOf2(T)(T x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    if (x.sign)
    {
        return false;
    }

    if (x.isNormal)
    {
        return !x.fraction;
    }
    else if (x.isSubnormal)
    {
        import core.bitop : popcnt;

        return popcnt(x.fraction) == 1;
    }

    return false;
}

///
@safe pure nothrow @nogc unittest
{
    static import std.math;

    assert(isPowerOf2(Binary32(1.0)));
    assert(isPowerOf2(Binary32(2.0)));
    assert(isPowerOf2(Binary32(0.5)));
    assert(isPowerOf2(Binary32(std.math.pow(2.0L, 96))));
    assert(isPowerOf2(Binary32(std.math.pow(2.0L, -77))));
    assert(!isPowerOf2(Binary32(-2.0)));
    assert(!isPowerOf2(Binary32(-0.5)));
    assert(!isPowerOf2(Binary32.zero));
    assert(!isPowerOf2(Binary32(4.315)));
    assert(!isPowerOf2(Binary32(1.0) / Binary32(3.0)));

    assert(!isPowerOf2(Binary32.nan));
    assert(!isPowerOf2(Binary32.infinity));

    assert(isPowerOf2(Binary32.min_normal / Binary32(4.0)));
    assert(!isPowerOf2(Binary32.min_normal / Binary32(3.0)));
}

///
@safe pure nothrow @nogc unittest
{
    static import std.math;

    assert(isPowerOf2(Binary64(1.0)));
    assert(isPowerOf2(Binary64(2.0)));
    assert(isPowerOf2(Binary64(0.5)));
    assert(isPowerOf2(Binary64(std.math.pow(2.0L, 96))));
    assert(isPowerOf2(Binary64(std.math.pow(2.0L, -77))));
    assert(!isPowerOf2(Binary64(-2.0)));
    assert(!isPowerOf2(Binary64(-0.5)));
    assert(!isPowerOf2(Binary64.zero));
    assert(!isPowerOf2(Binary64(4.315)));
    assert(!isPowerOf2(Binary64(1.0) / Binary64(3.0)));

    assert(!isPowerOf2(Binary64.nan));
    assert(!isPowerOf2(Binary64.infinity));

    assert(isPowerOf2(Binary64.min_normal / Binary64(4.0)));
    assert(!isPowerOf2(Binary64.min_normal / Binary64(3.0)));
}

///
bool isSubnormal(T)(T x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    return !x.exponent && x.fraction;
}

///
@safe pure nothrow @nogc unittest
{
    for (auto f = Binary32(1.0); !isSubnormal(f); f /= Binary32(2))
    {
        assert(!isZero(f));
    }
}

///
@safe pure nothrow @nogc unittest
{
    for (auto f = Binary32(1.0); !isSubnormal(f); f /= Binary32(2))
    {
        assert(!isZero(f));
    }
}

///
bool isZero(T)(T x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    return !x.exponent && !x.fraction;
}

///
@safe pure nothrow @nogc unittest
{
    assert(isZero(Binary32.zero));
    assert(isZero(-Binary32.zero));
    assert(!isZero(Binary32.infinity));
    assert(!isZero(Binary32.nan));
    assert(!isZero(Binary32(0.006)));
}

///
@safe pure nothrow @nogc unittest
{
    assert(isZero(Binary64.zero));
    assert(isZero(-Binary64.zero));
    assert(!isZero(Binary64.infinity));
    assert(!isZero(Binary64.nan));
    assert(!isZero(Binary64(0.006)));
}

import std.traits : isIntegral;

///
U copysign(T, U)(T to, const(U) from) pure nothrow @nogc @safe
        if ((isIEEE754Binary!T || isIntegral!T) && isIEEE754Binary!U)
{
    static if (isIntegral!T)
    {
        immutable to_ = U(to);
    }
    else
    {
        alias to_ = to;
    }
    return signbit(to_) == signbit(from) ? to_ : -to_;
}

///
@safe pure nothrow @nogc unittest
{
    immutable one = Binary32(1.0);

    assert(copysign(one, one) == one);
    assert(copysign(one, -Binary32.zero) == -one);
    assert(copysign(1UL, -one) == -one);
    assert(copysign(-one, -one) == -one);

    assert(copysign(Binary32.infinity, -one) == -Binary32.infinity);
    assert(isIdentical(copysign(Binary32.nan, one), Binary32.nan));
    assert(isIdentical(copysign(-Binary32.nan, one), Binary32.nan));
    assert(isIdentical(copysign(Binary32.nan, -one), -Binary32.nan));
}

///
@safe pure nothrow @nogc unittest
{
    immutable one = Binary64(1.0);

    assert(copysign(one, one) == one);
    assert(copysign(one, -Binary64.zero) == -one);
    assert(copysign(1UL, -one) == -one);
    assert(copysign(-one, -one) == -one);

    assert(copysign(Binary64.infinity, -one) == -Binary64.infinity);
    assert(isIdentical(copysign(Binary64.nan, one), Binary64.nan));
    assert(isIdentical(copysign(-Binary64.nan, one), Binary64.nan));
    assert(isIdentical(copysign(Binary64.nan, -one), -Binary64.nan));
}

///
T sgn(T)(const(T) x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    immutable one = T(1.0);
    return (x.isNaN || x.isZero) ? x : x.sign ? -one : one;
}

///
@safe pure nothrow @nogc unittest
{
    assert(sgn(Binary32(168.1234)) == Binary32(1.0));
    assert(sgn(Binary32(-168.1234)) == Binary32(-1.0));
    assert(sgn(Binary32.zero) == Binary32.zero);
    assert(sgn(-Binary32.zero) == -Binary32.zero);
}

///
@safe pure nothrow @nogc unittest
{
    assert(sgn(Binary64(168.1234)) == Binary64(1.0));
    assert(sgn(Binary64(-168.1234)) == Binary64(-1.0));
    assert(sgn(Binary64.zero) == Binary64.zero);
    assert(sgn(-Binary64.zero) == -Binary64.zero);
}

///
int signbit(T)(T x) pure nothrow @nogc @safe if (isIEEE754Binary!T)
{
    return x.sign;
}

///
@safe pure nothrow @nogc unittest
{
    assert(!signbit(Binary32.nan));
    assert(signbit(-Binary32.nan));
    assert(!signbit(Binary32(168.1234)));
    assert(signbit(Binary32(-168.1234)));
    assert(!signbit(Binary32.zero));
    assert(signbit(-Binary32.zero));
    assert(signbit(-Binary32.max));
    assert(!signbit(Binary32.max));
}

///
@safe pure nothrow @nogc unittest
{
    assert(!signbit(Binary64.nan));
    assert(signbit(-Binary64.nan));
    assert(!signbit(Binary64(168.1234)));
    assert(signbit(Binary64(-168.1234)));
    assert(!signbit(Binary64.zero));
    assert(signbit(-Binary64.zero));
    assert(signbit(-Binary64.max));
    assert(!signbit(Binary64.max));
}
