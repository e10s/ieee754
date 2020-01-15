module ieee754.math;

import ieee754.core : Binary32;

///
Binary32 fabs(Binary32 x) pure nothrow @nogc @safe
{
    return x.sign ? -x : x;
}

///
Binary32 sqrt(Binary32 x) pure nothrow @nogc @safe
{
    if (x.isNaN || x.isInfinity || x.isZero)
    {
        return x;
    }

    if (x.sign)
    {
        return -Binary32.nan; // Why -???
    }

    int exponent = x.exponent;
    uint mantissa = x.fraction;

    enum integerBit = 1U << Binary32.fractionBits;
    // Make normal form of 1.[fraction] * 2^E from subnormal
    if (!exponent) // Exponent of subnormal is 0
    {
        exponent = 1;

        foreach (_; 0 .. Binary32.fractionBits)
        {
            exponent--;
            mantissa <<= 1;

            if (mantissa & integerBit)
            {
                break;
            }
        }
    }
    else
    {
        mantissa |= integerBit;
    }

    enum int bias = cast(int) Binary32.bias;

    if ((exponent - bias) % 2)
    {
        exponent--;
        mantissa <<= 1;
    }

    assert((exponent - bias) % 2 == 0);

    immutable sqrtExponent = (exponent - bias) / 2 + bias;

    // [padding][integer: 2].[fraction: fractionBits][margin + for G: fractionBits + 2]
    immutable operandMantissa = cast(ulong) mantissa << (Binary32.fractionBits + 2);

    // [padding][integer: 1].[fraction: fractionBits][G: 1]
    uint sqrtMantissa;

    uint tempAdd, tempMulSub;

    foreach_reverse (i; 0 .. (Binary32.fractionBits + 1) + 1)
    {
        immutable twoBits = (operandMantissa >>> (i * 2)) & 0b11;
        tempMulSub <<= 2;
        tempMulSub |= twoBits;

        immutable bit = !(((tempAdd << 1) | 1) > tempMulSub);

        sqrtMantissa <<= 1;
        sqrtMantissa |= bit;

        immutable temp = (tempAdd << 1) | bit;
        tempAdd = temp + bit;
        tempMulSub -= temp * bit;
    }

    sqrtMantissa <<= 2;
    sqrtMantissa |= cast(bool) tempMulSub << 1;
    // [padding][integer: 1].[fraction: fractionBits][GRS: 3]
    assert(sqrtMantissa >>> (Binary32.fractionBits + 3) == 1);

    import ieee754.core : _rounder;

    return _rounder(0, sqrtExponent, sqrtMantissa);
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
//---------------------------

///
bool isFinite(Binary32 x) pure nothrow @nogc @safe
{
    return x.exponent != 0xFF;
}

///
bool isIdentical(Binary32 x, Binary32 y) pure nothrow @nogc @safe
{
    return x.sign == y.sign && x.exponent == y.exponent && x.exponent == y.exponent;
}

///
unittest
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
bool isInfinity(Binary32 x) pure nothrow @nogc @safe
{
    return x.exponent == 0xFF && !x.fraction;
}

///
bool isNaN(Binary32 x) pure nothrow @nogc @safe
{
    return x.exponent == 0xFF && x.fraction;
}

///
bool isNormal(Binary32 x) pure nothrow @nogc @safe
{
    return x.exponent && x.exponent != 0xFF;
}

///
bool isPowerOf2(Binary32 x) pure nothrow @nogc @safe
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
bool isSubnormal(Binary32 x) pure nothrow @nogc @safe
{
    return !x.exponent && x.fraction;
}

///
bool isZero(Binary32 x) pure nothrow @nogc @safe
{
    return !x.exponent && !x.fraction;
}

import std.traits : isIntegral;

///
Binary32 copysign(T)(T to, Binary32 from) pure nothrow @nogc @safe
        if (is(T : Binary32) || isIntegral!T)
{
    static if (isIntegral!T)
    {
        immutable to_ = Binary32(to);
    }
    else
    {
        alias to_ = to;
    }
    return signbit(to_) == signbit(from) ? to_ : -to_;
}

///
unittest
{
    immutable one = Binary32(1.0);

    assert(isIdentical(copysign(one, one), one));
    assert(isIdentical(copysign(1UL, -Binary32.zero), -one));
    assert(isIdentical(copysign(-one, -one), -one));

    assert(isIdentical(copysign(Binary32.infinity, -one), -Binary32.infinity));
    assert(isIdentical(copysign(Binary32.nan, one), Binary32.nan));
    assert(isIdentical(copysign(-Binary32.nan, one), Binary32.nan));
    assert(isIdentical(copysign(Binary32.nan, -one), -Binary32.nan));
}

///
Binary32 sgn(Binary32 x) pure nothrow @nogc @safe
{
    immutable one = Binary32(1.0);
    return (x.isNaN || x.isZero) ? x : x.sign ? -one : one;
}

///
unittest
{
    assert(isIdentical(sgn(Binary32(168.1234)), Binary32(1.0)));
    assert(isIdentical(sgn(Binary32(-168.1234)), Binary32(-1.0)));
    assert(isIdentical(sgn(Binary32.zero), Binary32.zero));
    assert(isIdentical(sgn(-Binary32.zero), -Binary32.zero));
}

///
int signbit(Binary32 x) pure nothrow @nogc @safe
{
    return x.sign;
}

///
unittest
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

unittest
{
    auto f = Binary32(1, 0b01111100, 0b010_0000_0000_0000_0000_0000);
    assert(f.value == -.15625);
    assert(f.fabs == -f);
    assert(f.isFinite);
    assert(!f.isInfinity);
    assert(!f.isNaN);
    assert(f.isNormal);
    assert(!f.isPowerOf2);
    assert(!f.isSubnormal);

    f.exponent = 0;
    f.fraction = 1;
    assert(!f.isNormal);
    assert(!f.isPowerOf2);
    assert(f.isSubnormal);
    f.sign = 0;
    assert(f.isPowerOf2);
    f.fraction = 3;
    assert(!f.isPowerOf2);

    f = Binary32(128);
    assert(f.isPowerOf2);

    f = Binary32(0);
    assert(!f.isNormal);
    assert(!f.isPowerOf2);
    assert(!f.isSubnormal);

    f = Binary32(float.nan);
    assert(f.fabs.isNaN);
    assert(!f.isFinite);
    assert(!f.isInfinity);
    assert(f.isNaN);
    assert(!f.isNormal);
    assert(!f.isPowerOf2);
    assert(!f.isSubnormal);

    f = Binary32(float.infinity);
    assert(f.fabs == f);
    assert(!f.isFinite);
    assert(f.isInfinity);
    assert(!f.isPowerOf2);
    f.sign = 1;
    assert(f.fabs == -f);
    assert(f.isInfinity);
    assert(!f.isNaN);
    assert(!f.isNormal);
    assert(!f.isSubnormal);
}
