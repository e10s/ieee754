module ieee754.core;

import ieee754.type, ieee754.math;

package Binary32 add(Binary32 lhs, Binary32 rhs) pure nothrow @nogc @safe
{
    immutable lhsMagnitude = (lhs.exponent << Binary32.fractionBits) | lhs.fraction;
    immutable rhsMagnitude = (rhs.exponent << Binary32.fractionBits) | rhs.fraction;

    if (lhs.sign != rhs.sign && lhsMagnitude == rhsMagnitude)
    {
        return Binary32.zero;
    }

    immutable larger = lhsMagnitude > rhsMagnitude ? lhs : rhs;
    immutable smaller = larger == lhs ? rhs : lhs;

    int largerExponent = larger.exponent;
    int smallerExponent = smaller.exponent;

    // [padding][integer: 1].[fraction: fractionBits][GRS: 3]
    uint largerMantissa, smallerMantissa;

    enum implicitLeadingBit = 1U << Binary32.fractionBits;
    if (larger.isNormal)
    {
        largerMantissa = (implicitLeadingBit | larger.fraction) << 3;
    }
    else
    {
        largerExponent = 1;
        largerMantissa = larger.fraction << 3;
    }

    if (smaller.isNormal)
    {
        smallerMantissa = (implicitLeadingBit | smaller.fraction) << 3;
    }
    else
    {
        smallerExponent = 1;
        smallerMantissa = smaller.fraction << 3;
    }
    assert(largerExponent >= smallerExponent);

    // preliminary shift
    immutable shift = largerExponent - smallerExponent;
    foreach (_; 0 .. shift)
    {
        immutable stickyBit = smallerMantissa & 1;
        smallerMantissa >>>= 1;
        smallerMantissa |= stickyBit;
    }

    immutable smallerSign = (larger.sign ? -1 : 1) * (smaller.sign ? -1 : 1);
    immutable sumMantissa = largerMantissa + smallerSign * smallerMantissa;
    assert(cast(int) sumMantissa > 0);

    immutable sumSign = larger.sign;
    auto sumExponent = largerExponent;

    return _rounder(sumSign, cast(ubyte) sumExponent, sumMantissa);
}

package Binary32 mul(Binary32 lhs, Binary32 rhs) pure nothrow @nogc @safe
{
    immutable prodSign = lhs.sign ^ rhs.sign;

    if (lhs.isZero || rhs.isZero)
    {
        auto z = Binary32.zero;
        z.sign = prodSign;
        return z;
    }

    if (lhs.isInfinity || rhs.isInfinity)
    {
        auto inf = Binary32.infinity;
        inf.sign = prodSign;
        return inf;
    }

    immutable lhs2 = Fixed!Binary32(lhs);
    immutable rhs2 = Fixed!Binary32(rhs);

    immutable prodExponent = lhs2.exponentUnbiased + rhs2.exponentUnbiased + Binary32.bias;

    // [padding][integer: 2].[fraction: fractionBits][extra: fractionBits]
    ulong prodMantissa = cast(ulong) lhs2.mantissaNormalized * cast(ulong) rhs2.mantissaNormalized;
    immutable extraMask = (1UL << Fixed!Binary32.fractionBits) - 1;
    immutable hasExtra = cast(bool) prodMantissa & extraMask;
    prodMantissa >>>= Fixed!Binary32.fractionBits;

    if (hasExtra)
    {
        prodMantissa |= 1;
    }

    // [padding][integer: 2].[fraction: fractionBits]
    return _rounder(prodSign, prodExponent, cast(uint) prodMantissa);
}

package Binary32 div(Binary32 lhs, Binary32 rhs) pure nothrow @nogc @safe
{
    immutable quotSign = lhs.sign ^ rhs.sign;

    if (lhs.isZero || rhs.isInfinity)
    {
        auto z = Binary32.zero;
        z.sign = quotSign;
        return z;
    }

    if (lhs.isInfinity || rhs.isZero)
    {
        auto inf = Binary32.infinity;
        inf.sign = quotSign;
        return inf;
    }

    int lhsExponent = lhs.exponent;
    int rhsExponent = rhs.exponent;
    uint lhsFraction = lhs.fraction;
    uint rhsFraction = rhs.fraction;

    // Make normal form of 1.[fraction] * 2^E from subnormal
    void normalizeSubnormal(ref int exponent, ref uint fraction)
    in
    {
        assert(!exponent); // Exponent of subnormal is 0
    }
    do
    {
        exponent = 1;
        uint mantissa = fraction;

        enum integerBit = 1U << Binary32.fractionBits;
        enum fracMask = integerBit - 1;
        foreach (_; 0 .. Binary32.fractionBits)
        {
            exponent--;
            mantissa <<= 1;

            if (mantissa & integerBit)
            {
                break;
            }
        }

        fraction = mantissa & fracMask;
    }

    if (!lhsExponent) // lhs is subnormal
    {
        normalizeSubnormal(lhsExponent, lhsFraction);
    }

    if (!rhsExponent) // rhs is subnormal
    {
        normalizeSubnormal(rhsExponent, rhsFraction);
    }

    immutable quotExponent = lhsExponent - rhsExponent + Binary32.bias;

    enum implicitLeadingBit = 1U << Binary32.fractionBits;
    immutable lhsMantissa = implicitLeadingBit | lhsFraction;
    immutable rhsMantissa = implicitLeadingBit | rhsFraction;

    // [padding][integer: 1].[fraction: fractionBits][margin: fractionBits][margin for GRS: 3]
    immutable dividend = cast(ulong) lhsMantissa << (Binary32.fractionBits + 3);

    // [padding][integer: 1].[fraction: fractionBits][GRS: 3]
    ulong quotMantissa = dividend / rhsMantissa;

    immutable stickyBit = dividend != quotMantissa * rhsMantissa;
    quotMantissa |= stickyBit;
    assert(quotMantissa >>> (Binary32.fractionBits - 1 + 3));

    return _rounder(quotSign, quotExponent, cast(uint) quotMantissa);
}

private struct Fixed(Float)
{
    alias MantType = typeof(Float.fraction);

    bool sign;
    int exponentUnbiased;
    MantType mantissaNormalized;

    enum grsBits = 3;
    enum fractionBits = Float.fractionBits + grsBits;
    enum integerBit = MantType(1) << fractionBits;

    this(Float value) pure nothrow @nogc @safe
    in
    {
        assert(value.exponent < value.exponent.max);
    }
    do
    {
        sign = value.sign;
        immutable isNormal = cast(bool) value.exponent;
        exponentUnbiased = isNormal ? value.exponent : 1;
        exponentUnbiased -= int(Float.bias);
        mantissaNormalized = value.fraction << 3;

        if (isNormal)
        {
            mantissaNormalized |= integerBit;
        }

        normalize();
    }

    void normalize() pure nothrow @nogc @safe
    {
        if (fractionPart)
        {
            while (!integerPart)
            {
                shiftMantissaToLeft(1);
            }
        }

        while (integerPart > 1)
        {
            shiftMantissaToRight(1);
        }

        if (!mantissaNormalized)
        {
            exponentUnbiased = 0;
        }
    }

    void shiftMantissaToLeft(size_t shift) pure nothrow @nogc @safe
    {
        exponentUnbiased -= cast(int) shift;

        foreach (_; 0 .. shift)
        {
            mantissaNormalized <<= 1;
        }
    }

    void shiftMantissaToRight(size_t shift) pure nothrow @nogc @safe
    {
        exponentUnbiased += cast(int) shift;

        foreach (_; 0 .. shift)
        {
            immutable stickyBit = mantissaNormalized & 1;
            mantissaNormalized >>>= 1;
            mantissaNormalized |= stickyBit;
        }
    }

    MantType integerPart() const pure nothrow @nogc @safe @property
    {
        return mantissaNormalized >>> fractionBits;
    }

    MantType fractionPart() const pure nothrow @nogc @safe @property
    {
        enum fracMask = integerBit - 1;
        return mantissaNormalized & fracMask;
    }
}

pure nothrow @nogc @safe unittest
{
    immutable z = Fixed!Binary32(Binary32(-0.0));
    assert(z.sign == 1);
    assert(z.exponentUnbiased == 0);
    assert(z.mantissaNormalized == 0);

    immutable a = Fixed!Binary32(Binary32(3.1415927));
    assert(a.sign == 0);
    assert(a.exponentUnbiased == 1);
    assert(a.mantissaNormalized == 0b1_100_1001_0000_1111_1101_1011_000);

    immutable b = Fixed!Binary32(-Binary32(float.min_normal / 2));
    assert(b.sign == 1);
    assert(b.exponentUnbiased == -126 - 1);
    assert(b.mantissaNormalized == 1 << 26);
}

private struct _RounderImpl
{
    bool sign;
    int exponent;
    uint mantissa; // [padding][reserved for carry: 1][integer: 1].[fraction: fractionBits][GRS: 3]

    // param mantissa: [padding][reserved for carry: 1][integer: 1].[fraction: fractionBits][GRS: 3]
    this(bool sign, int exponent, uint mantissa) pure nothrow @nogc @safe
    {
        this.sign = sign;

        immutable integer = mantissa >>> (Binary32.fractionBits + 3);

        // Normalize temporarily
        if (integer > 1)
        {
            shiftMantissaToLeftBy1(exponent, mantissa);
        }
        else if (!integer)
        {
            enum integerBit = 1U << (Binary32.fractionBits + 3);

            foreach (_; 0 .. Binary32.fractionBits + 3)
            {
                exponent--;
                mantissa <<= 1;

                if (mantissa & integerBit)
                {
                    break;
                }
            }
        }

        // Subnormalize if needed
        if (exponent < 1)
        {
            // Make 0.xxxx * 2^1
            immutable shift = 1 - exponent;
            foreach (_; 0 .. shift)
            {
                shiftMantissaToLeftBy1(exponent, mantissa);
            }
            assert(exponent == 1);
        }

        this.exponent = exponent;
        this.mantissa = mantissa;
    }

    void shiftMantissaToLeftBy1(ref int exp, ref uint mant) pure nothrow @nogc @safe
    {
        immutable stickyBit = mant & 1;
        exp++;
        mant >>>= 1;
        mant |= stickyBit;
    }

    uint integerPart() const pure nothrow @nogc @safe @property
    {
        return mantissa >>> (Binary32.fractionBits + 3);
    }

    uint fractionPart() const pure nothrow @nogc @safe @property
    {
        enum fracMask = (1 << Binary32.fractionBits) - 1;
        return (mantissa >>> 3) & fracMask;
    }

    void round() pure nothrow @nogc @safe
    {
        mantissa = roundImpl(sign, mantissa, Binary32.fractionBits);

        if (integerPart > 1)
        {
            assert(integerPart == 0b10 || integerPart == 0b11);
            shiftMantissaToLeftBy1(exponent, mantissa);
        }
    }

    bool overflow() const pure nothrow @nogc @safe @property
    {
        return exponent > 0xFE;
    }

    bool underflow() const pure nothrow @nogc @safe @property
    {
        return exponent <= 1 && !integerPart;
    }

    Binary32 result() const pure nothrow @nogc @safe @property
    {
        if (overflow)
        {
            return sign ? -Binary32.infinity : Binary32.infinity;
        }
        assert(exponent < 0xFF);
        assert(exponent > 0);

        return Binary32(sign, underflow ? 0 : cast(ubyte) exponent, fractionPart);
    }

    string toString() const pure @safe
    {
        import std.format : format;

        immutable fmt = format!"exp: %%0%sb, int: %%0%sb, frac: %%0%sb, grs: %%0%sb"(
                Binary32.exponentBits, 2, Binary32.fractionBits, 3);
        return format!fmt(exponent, integerPart, fractionPart, mantissa & 0b111);
    }
}

package uint roundImpl(bool sign, uint q26, uint resultFractionBits) pure nothrow @nogc @safe
in
{
    assert(resultFractionBits <= Binary32.fractionBits);
}
out (r)
{
    immutable extraBits = Binary32.fractionBits - resultFractionBits + 3;
    assert((r >>> extraBits) << extraBits == r);
}
do
{
    import std.math : FloatingPointControl;

    immutable extraBits = Binary32.fractionBits - resultFractionBits + 3;
    immutable hasExtra = q26 != (q26 >>> extraBits) << extraBits;

    if (!hasExtra)
    {
        return q26;
    }

    bool roundToInf;

    switch (FloatingPointControl.rounding)
    {
    case FloatingPointControl.roundToNearest:
        immutable shift = Binary32.fractionBits - resultFractionBits;

        immutable ulp_r_s = q26 & ((0b1011 << shift) | ((1U << shift) - 1));
        immutable g = q26 & (0b100 << shift);
        roundToInf = g && ulp_r_s; // something magic
        break;
    case FloatingPointControl.roundDown:
        roundToInf = sign;
        break;
    case FloatingPointControl.roundUp:
        roundToInf = !sign;
        break;
    case FloatingPointControl.roundToZero:
        break;
    default:
        assert(0);
    }

    return ((q26 >>> extraBits) + roundToInf) << extraBits;
}

nothrow @nogc @safe unittest
{
    import std.math : FloatingPointControl;

    pragma(inline, false);
    FloatingPointControl fpctrl;

    {
        fpctrl.rounding = FloatingPointControl.roundToNearest;

        assert(roundImpl(0, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl(0, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl(0, 0b10_10100, Binary32.fractionBits - 2) == 0b11_00000);
        assert(roundImpl(0, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl(0, 0b11_100, Binary32.fractionBits) == 0b100_000);

        assert(roundImpl(1, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl(1, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl(1, 0b10_10100, Binary32.fractionBits - 2) == 0b11_00000);
        assert(roundImpl(1, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl(1, 0b11_100, Binary32.fractionBits) == 0b100_000);
    }

    {
        fpctrl.rounding = FloatingPointControl.roundDown;

        assert(roundImpl(0, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl(0, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl(0, 0b10_10100, Binary32.fractionBits - 2) == 0b10_00000);
        assert(roundImpl(0, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl(0, 0b11_100, Binary32.fractionBits) == 0b11_000);

        assert(roundImpl(1, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl(1, 0b10_0100, Binary32.fractionBits - 1) == 0b11_0000);
        assert(roundImpl(1, 0b10_10100, Binary32.fractionBits - 2) == 0b11_00000);
        assert(roundImpl(1, 0b10_100000, Binary32.fractionBits - 3) == 0b11_000000);
        assert(roundImpl(1, 0b11_100, Binary32.fractionBits) == 0b100_000);
    }

    {
        fpctrl.rounding = FloatingPointControl.roundUp;

        assert(roundImpl(0, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl(0, 0b10_0100, Binary32.fractionBits - 1) == 0b11_0000);
        assert(roundImpl(0, 0b10_10100, Binary32.fractionBits - 2) == 0b11_00000);
        assert(roundImpl(0, 0b10_100000, Binary32.fractionBits - 3) == 0b11_000000);
        assert(roundImpl(0, 0b11_100, Binary32.fractionBits) == 0b100_000);

        assert(roundImpl(1, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl(1, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl(1, 0b10_10100, Binary32.fractionBits - 2) == 0b10_00000);
        assert(roundImpl(1, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl(1, 0b11_100, Binary32.fractionBits) == 0b11_000);
    }

    {
        fpctrl.rounding = FloatingPointControl.roundToZero;

        assert(roundImpl(0, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl(0, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl(0, 0b10_10100, Binary32.fractionBits - 2) == 0b10_00000);
        assert(roundImpl(0, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl(0, 0b11_100, Binary32.fractionBits) == 0b11_000);

        assert(roundImpl(1, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl(1, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl(1, 0b10_10100, Binary32.fractionBits - 2) == 0b10_00000);
        assert(roundImpl(1, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl(1, 0b11_100, Binary32.fractionBits) == 0b11_000);
    }
}

package Binary32 _rounder(bool sign, int exponent, uint mantissa) pure nothrow @nogc @safe
{
    auto r = _RounderImpl(sign, exponent, mantissa);

    if (r.overflow) // unrecoverable
    {
        return r.result;
    }

    r.round();
    return r.result;
}
