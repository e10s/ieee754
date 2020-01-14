module ieee754.math;

import ieee754.core : Binary32;

///
Binary32 fabs(Binary32 x) pure nothrow @nogc @safe
{
    return x.sign ? Binary32(0, x.exponent, x.fraction) : x;
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
