module ieee754.core;

import ieee754.type, ieee754.math;

package T add(T)(const(T) lhs, const(T) rhs) pure nothrow @nogc @safe
        if (isIEEE754Binary!T)
in(isFinite(lhs))
in(isFinite(rhs))
{
    immutable cmpResult = cmp(fabs(lhs), fabs(rhs));

    immutable larger = cmpResult > 0 ? lhs : rhs;
    immutable smaller = isIdentical(larger, lhs) ? rhs : lhs;

    immutable larger2 = Fixed!T(larger);
    auto smaller2 = Fixed!T(smaller);

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

    return round(Fixed!T(sumSign, sumExponent, sumMantissa));
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

private struct Ucent
{
    ulong high, low;
    this(ulong high, ulong low) pure nothrow @nogc @safe
    {
        this.high = high;
        this.low = low;
    }

    Ucent opBinary(string op)(size_t shift) const pure nothrow @nogc @safe
            if (op == ">>" || op == ">>>")
    {
        if (shift >= 128)
        {
            return Ucent(0UL, 0UL);
        }

        if (shift < 64)
        {
            immutable newHigh = high >>> shift;
            immutable toLow = (high - (newHigh << shift)) << (64 - cast(int) shift);
            return Ucent(newHigh, toLow | (low >>> shift));
        }
        else
        {
            return Ucent(0UL, high >>> (shift - 64));
        }
    }

    pure nothrow @nogc @safe unittest
    {
        assert(Ucent(9, 16) >> 3 == Ucent(1, (1UL << 61) + 2));
        assert(Ucent(9, 16) >> 65 == Ucent(0, 4));
        assert(Ucent(9, 16) >> 300 == Ucent(0, 0));
    }

    int opCmp(Ucent x) const pure nothrow @nogc @safe
    {
        immutable t = (high > x.high) - (high < x.high);
        return t ? t : (low > x.low) - (low < x.low);
    }

    pure nothrow @nogc @safe unittest
    {
        assert(Ucent(4, 2) < Ucent(11, 9));
        assert(Ucent(4, 2) < Ucent(4, 9));
        assert(Ucent(50, 2) > Ucent(4, 9));
        assert(Ucent(50, 2) == Ucent(50, 2));
    }
}

package Ucent mul128(ulong a, ulong b) pure nothrow @nogc @safe
{
    auto hi32(ulong x)
    {
        return x >>> 32;
    }

    auto lo32(ulong x)
    {
        return x & 0xFFFF_FFFFUL;
    }

    immutable tmpHi = hi32(a) * hi32(b);
    immutable tmpMid = hi32(a) * lo32(b) + lo32(a) * hi32(b);
    immutable tmpLo = lo32(a) * lo32(b);

    immutable prodLo = lo32(tmpLo);
    immutable tmpProdMidLo = hi32(tmpLo) + lo32(tmpMid);
    immutable prodMidLo = lo32(tmpProdMidLo);

    immutable lowProduct = (prodMidLo << 32) | prodLo;

    immutable carryProdMidLo = hi32(tmpProdMidLo);
    immutable prodMidHi = hi32(tmpMid);
    immutable highProduct = tmpHi + prodMidHi + carryProdMidLo;

    return Ucent(highProduct, lowProduct);
}

package Binary64 mul(Binary64 lhs, Binary64 rhs) pure nothrow @nogc @safe
in(isFinite(lhs))
in(isFinite(rhs))
{
    immutable lhs2 = Fixed!Binary64(lhs);
    immutable rhs2 = Fixed!Binary64(rhs);

    immutable prodSign = lhs2.sign ^ rhs2.sign;
    immutable prodExponent = lhs2.exponentUnbiased + rhs2.exponentUnbiased;

    immutable prod = mul128(lhs2.mantissa, rhs2.mantissa);
    enum extraMask = (1UL << 55) - 1;
    immutable stickyBit = cast(bool)(prod.low & extraMask);
    immutable prodMantissa = (prod.high << 9) | (prod.low >>> 55) | stickyBit;

    return round(Fixed!Binary64(prodSign, prodExponent, prodMantissa));
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

package Binary64 div(Binary64 lhs, Binary64 rhs) pure nothrow @nogc @safe
in(isFinite(lhs))
in(isFinite(rhs))
{
    immutable lhs2 = Fixed!Binary64(lhs);
    immutable rhs2 = Fixed!Binary64(rhs);

    immutable quotSign = lhs2.sign ^ rhs2.sign;
    immutable quotExponent = lhs2.exponentUnbiased - rhs2.exponentUnbiased;
    immutable dividend = mul128(lhs2.mantissa,
            Fixed!Binary64.MantType(1) << Fixed!Binary64.fractionBits);

    ulong q;
    Ucent prod;
    foreach_reverse (i; 0 .. Fixed!Binary64.fractionBits + 1)
    {
        immutable bit = Fixed!Binary64.MantType(1) << i;
        immutable newQ = q | bit;
        prod = mul128(newQ, rhs2.mantissa);

        if (dividend == prod)
        {
            q = newQ;
            break;
        }
        if (dividend > prod)
        {
            q = newQ;
        }
    }

    immutable stickyBit = dividend != prod;
    immutable quotMantissa = q | stickyBit;
    assert(quotMantissa >>> (Fixed!Binary64.fractionBits - 1));

    return round(Fixed!Binary64(quotSign, quotExponent, quotMantissa));
}

package struct Fixed(Float)
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
        return exponentUnbiased >= Float.max_exp;
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

package Float round(Float)(Fixed!Float r) pure nothrow @nogc @safe @property
{
    alias ExpType = typeof(Float.exponent);
    r.normalize();
    r.subnormalize();

    if (r.overflow) // unrecoverable
    {
        return r.sign ? -Float.infinity : Float.infinity;
    }

    r.mantissa = roundImpl!Float(r.sign, r.mantissa, Float.fractionBits);

    r.normalize();
    r.subnormalize();

    if (r.overflow)
    {
        return r.sign ? -Float.infinity : Float.infinity;
    }

    assert(r.exponentUnbiased < Float.max_exp);
    assert(r.exponentBiased > 0);

    return Float(r.sign, r.underflow ? 0 : cast(ExpType) r.exponentBiased, r.fractionPart >>> 3);
}

package Float.FractionType roundImpl(Float)(bool sign,
        Float.FractionType qFractionBitsWithGRS, uint resultFractionBits) pure nothrow @nogc @safe
in
{
    assert(resultFractionBits <= Float.fractionBits);
}
out (r)
{
    immutable extraBits = Float.fractionBits - resultFractionBits + 3;
    assert((r >>> extraBits) << extraBits == r);
}
do
{
    import std.math : FloatingPointControl;

    immutable extraBits = Float.fractionBits - resultFractionBits + 3;
    immutable hasExtra = qFractionBitsWithGRS != (qFractionBitsWithGRS >>> extraBits) << extraBits;

    if (!hasExtra)
    {
        return qFractionBitsWithGRS;
    }

    bool roundToInf;

    switch (FloatingPointControl.rounding)
    {
    case FloatingPointControl.roundToNearest:
        immutable shift = Float.fractionBits - resultFractionBits;

        immutable ulp_r_s = qFractionBitsWithGRS & (
                (Float.FractionType(0b1011) << shift) | ((Float.FractionType(1) << shift) - 1));
        immutable g = qFractionBitsWithGRS & (Float.FractionType(0b100) << shift);
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

    return ((qFractionBitsWithGRS >>> extraBits) + roundToInf) << extraBits;
}

nothrow @nogc @safe unittest
{
    import std.math : FloatingPointControl;

    pragma(inline, false);
    FloatingPointControl fpctrl;

    {
        fpctrl.rounding = FloatingPointControl.roundToNearest;

        assert(roundImpl!Binary32(0, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl!Binary32(0, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl!Binary32(0, 0b10_10100, Binary32.fractionBits - 2) == 0b11_00000);
        assert(roundImpl!Binary32(0, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl!Binary32(0, 0b11_100, Binary32.fractionBits) == 0b100_000);

        assert(roundImpl!Binary32(1, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl!Binary32(1, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl!Binary32(1, 0b10_10100, Binary32.fractionBits - 2) == 0b11_00000);
        assert(roundImpl!Binary32(1, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl!Binary32(1, 0b11_100, Binary32.fractionBits) == 0b100_000);
    }

    {
        fpctrl.rounding = FloatingPointControl.roundDown;

        assert(roundImpl!Binary32(0, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl!Binary32(0, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl!Binary32(0, 0b10_10100, Binary32.fractionBits - 2) == 0b10_00000);
        assert(roundImpl!Binary32(0, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl!Binary32(0, 0b11_100, Binary32.fractionBits) == 0b11_000);

        assert(roundImpl!Binary32(1, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl!Binary32(1, 0b10_0100, Binary32.fractionBits - 1) == 0b11_0000);
        assert(roundImpl!Binary32(1, 0b10_10100, Binary32.fractionBits - 2) == 0b11_00000);
        assert(roundImpl!Binary32(1, 0b10_100000, Binary32.fractionBits - 3) == 0b11_000000);
        assert(roundImpl!Binary32(1, 0b11_100, Binary32.fractionBits) == 0b100_000);
    }

    {
        fpctrl.rounding = FloatingPointControl.roundUp;

        assert(roundImpl!Binary32(0, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl!Binary32(0, 0b10_0100, Binary32.fractionBits - 1) == 0b11_0000);
        assert(roundImpl!Binary32(0, 0b10_10100, Binary32.fractionBits - 2) == 0b11_00000);
        assert(roundImpl!Binary32(0, 0b10_100000, Binary32.fractionBits - 3) == 0b11_000000);
        assert(roundImpl!Binary32(0, 0b11_100, Binary32.fractionBits) == 0b100_000);

        assert(roundImpl!Binary32(1, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl!Binary32(1, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl!Binary32(1, 0b10_10100, Binary32.fractionBits - 2) == 0b10_00000);
        assert(roundImpl!Binary32(1, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl!Binary32(1, 0b11_100, Binary32.fractionBits) == 0b11_000);
    }

    {
        fpctrl.rounding = FloatingPointControl.roundToZero;

        assert(roundImpl!Binary32(0, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl!Binary32(0, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl!Binary32(0, 0b10_10100, Binary32.fractionBits - 2) == 0b10_00000);
        assert(roundImpl!Binary32(0, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl!Binary32(0, 0b11_100, Binary32.fractionBits) == 0b11_000);

        assert(roundImpl!Binary32(1, 0b10_000, Binary32.fractionBits) == 0b10_000);
        assert(roundImpl!Binary32(1, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl!Binary32(1, 0b10_10100, Binary32.fractionBits - 2) == 0b10_00000);
        assert(roundImpl!Binary32(1, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl!Binary32(1, 0b11_100, Binary32.fractionBits) == 0b11_000);
    }
}
