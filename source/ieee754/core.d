module ieee754.core;

import ieee754.type, ieee754.math;

package Binary32 add(Binary32 lhs, Binary32 rhs) pure nothrow @nogc @safe
in(isFinite(lhs))
in(isFinite(rhs))
{
    immutable cmpResult = cmp(fabs(lhs), fabs(rhs));

    immutable larger = cmpResult > 0 ? lhs : rhs;
    immutable smaller = isIdentical(larger, lhs) ? rhs : lhs;

    immutable larger2 = Fixed!Binary32(larger);
    auto smaller2 = Fixed!Binary32(smaller);

    // preliminary shift
    if (smaller2.mantissa == 0)
    {
        smaller2.exponentUnbiased = larger2.exponentUnbiased;
    }
    else
    {
        assert(larger2.exponentUnbiased >= smaller2.exponentUnbiased);

        immutable shift = larger2.exponentUnbiased - smaller2.exponentUnbiased;
        smaller2.shiftMantissaToRight(shift);
    }

    assert(larger2.exponentUnbiased == smaller2.exponentUnbiased);
    immutable sumExponent = larger2.exponentUnbiased;

    immutable smallerSign = (larger2.sign ? -1 : 1) * (smaller2.sign ? -1 : 1);
    immutable sumMantissa = larger2.mantissa + smallerSign * smaller2.mantissa;
    assert(cast(int) sumMantissa >= 0);
    immutable sumSign = {
        import std.math : FloatingPointControl;

        if (sumMantissa == 0)
        {
            if (FloatingPointControl.rounding == FloatingPointControl.roundDown)
            {
                return larger2.sign || smaller2.sign;
            }
            else
            {
                return larger2.sign && smaller2.sign;
            }
        }
        else
        {
            return larger2.sign;
        }
    }();

    return round(Fixed!Binary32(sumSign, sumExponent, sumMantissa));
}

package Binary32 mul(Binary32 lhs, Binary32 rhs) pure nothrow @nogc @safe
in(isFinite(lhs))
in(isFinite(rhs))
{
    immutable lhs2 = Fixed!Binary32(lhs);
    immutable rhs2 = Fixed!Binary32(rhs);

    immutable prodSign = lhs2.sign ^ rhs2.sign;
    immutable prodExponent = lhs2.exponentUnbiased + rhs2.exponentUnbiased;

    // [padding][integer: 2].[fraction: fractionBits][extra: fractionBits]
    immutable p = cast(ulong) lhs2.mantissa * cast(ulong) rhs2.mantissa;
    enum extraMask = (1UL << Fixed!Binary32.fractionBits) - 1;
    immutable stickyBit = cast(bool)(p & extraMask);
    immutable prodMantissa = cast(uint)(p >>> Fixed!Binary32.fractionBits) | stickyBit;

    return round(Fixed!Binary32(prodSign, prodExponent, prodMantissa));
}

package Binary32 div(Binary32 lhs, Binary32 rhs) pure nothrow @nogc @safe
in(isFinite(lhs))
in(isFinite(rhs))
{
    immutable lhs2 = Fixed!Binary32(lhs);
    immutable rhs2 = Fixed!Binary32(rhs);

    immutable quotSign = lhs2.sign ^ rhs2.sign;
    immutable quotExponent = lhs2.exponentUnbiased - rhs2.exponentUnbiased;

    // [padding][integer: 1].[fraction: fractionBits][margin: fractionBits]
    immutable dividend = cast(ulong) lhs2.mantissa << Fixed!Binary32.fractionBits;

    // [padding][integer: 1].[fraction: fractionBits]
    immutable q = dividend / rhs2.mantissa;
    immutable stickyBit = dividend != q * rhs2.mantissa;
    immutable quotMantissa = cast(uint) q | stickyBit;
    assert(quotMantissa >>> (Fixed!Binary32.fractionBits - 1));

    return round(Fixed!Binary32(quotSign, quotExponent, quotMantissa));
}

private struct Fixed(Float)
{
    alias MantType = typeof(Float.fraction);

    bool sign;
    int exponentUnbiased;
    MantType mantissa;

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
        mantissa = value.fraction << 3;

        if (isNormal)
        {
            mantissa |= integerBit;
        }

        normalize();
    }

    // store as is
    this(bool sign, int exponentUnbiased, MantType mantissa) pure nothrow @nogc @safe
    {
        this.sign = sign;
        this.exponentUnbiased = exponentUnbiased;
        this.mantissa = mantissa;
    }

    int exponentBiased() const pure nothrow @nogc @safe @property
    {
        return exponentUnbiased + Float.bias;
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

        if (!mantissa)
        {
            exponentUnbiased = 1 - int(Float.bias);
        }
    }

    void subnormalize()
    {
        if (exponentBiased < 1)
        {
            immutable shift = 1 - exponentBiased;
            shiftMantissaToRight(shift);
            assert(exponentBiased == 1);
        }
    }

    void shiftMantissaToLeft(size_t shift) pure nothrow @nogc @safe
    {
        exponentUnbiased -= cast(int) shift;

        foreach (_; 0 .. shift)
        {
            mantissa <<= 1;
        }
    }

    void shiftMantissaToRight(size_t shift) pure nothrow @nogc @safe
    {
        exponentUnbiased += cast(int) shift;

        foreach (_; 0 .. shift)
        {
            immutable stickyBit = mantissa & 1;
            mantissa >>>= 1;
            mantissa |= stickyBit;
        }
    }

    MantType integerPart() const pure nothrow @nogc @safe @property
    {
        return mantissa >>> fractionBits;
    }

    MantType fractionPart() const pure nothrow @nogc @safe @property
    {
        enum fracMask = integerBit - 1;
        return mantissa & fracMask;
    }

    bool overflow() const pure nothrow @nogc @safe @property
    {
        return exponentBiased > 0xFE;
    }

    bool underflow() const pure nothrow @nogc @safe @property
    {
        return exponentBiased <= 1 && !integerPart;
    }

    string toString() const pure @safe
    {
        import std.format : format;

        immutable fmt = format!"expUB: %%s, int: %%b, frac: %%0%sb"(Float.fractionBits);
        return format!fmt(exponentUnbiased, integerPart, fractionPart);
    }
}

pure nothrow @nogc @safe unittest
{
    immutable z = Fixed!Binary32(Binary32(-0.0));
    assert(z.sign == 1);
    assert(z.exponentBiased == 1);
    assert(z.mantissa == 0);

    immutable a = Fixed!Binary32(Binary32(3.1415927));
    assert(a.sign == 0);
    assert(a.exponentUnbiased == 1);
    assert(a.mantissa == 0b1_100_1001_0000_1111_1101_1011_000);

    immutable b = Fixed!Binary32(-Binary32(float.min_normal / 2));
    assert(b.sign == 1);
    assert(b.exponentUnbiased == -126 - 1);
    assert(b.mantissa == 1 << 26);

    auto c = Fixed!Binary32(Binary32(float.min_normal / 4));
    assert(c.sign == 0);
    assert(c.exponentUnbiased == -126 - 2);
    assert(c.mantissa == 1 << c.fractionBits);
    c.subnormalize();
    assert(c.exponentUnbiased == -126);
    assert(c.mantissa == 1 << 24);
    c.normalize();
    assert(c.exponentUnbiased == -126 - 2);
    assert(c.mantissa == 1 << c.fractionBits);
}

private Float round(Float)(Fixed!Float r) pure nothrow @nogc @safe @property
{
    alias ExpType = typeof(Float.exponent);
    r.normalize();
    r.subnormalize();

    if (r.overflow) // unrecoverable
    {
        return r.sign ? -Float.infinity : Float.infinity;
    }

    r.mantissa = roundImpl(r.sign, r.mantissa, Float.fractionBits);

    r.normalize();
    r.subnormalize();

    if (r.overflow)
    {
        return r.sign ? -Float.infinity : Float.infinity;
    }

    assert(r.exponentBiased < 0xFF);
    assert(r.exponentBiased > 0);

    return Float(r.sign, r.underflow ? 0 : cast(ExpType) r.exponentBiased, r.fractionPart >>> 3);
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
