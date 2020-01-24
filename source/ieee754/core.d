module ieee754.core;

import ieee754.math;

/// Single precision FP
struct Binary32
{
    // borrowed from std.bitmanip.FloatRep
    ///
    union
    {
        float value;

        import std.bitmanip : bitfields;

        mixin(bitfields!(uint, "fraction", fractionBits, ubyte, "exponent",
                exponentBits, bool, "sign", signBits));
    }
    ///
    this(float value) pure nothrow @nogc @safe
    {
        this.value = value;
    }

    ///
    this(bool sign, ubyte exponent, uint fraction) pure nothrow @nogc @safe
    {
        this.sign = sign;
        this.exponent = exponent;
        this.fraction = fraction;
    }

    ///
    enum uint bias = 127, fractionBits = 23, exponentBits = 8, signBits = 1;

    /// Initializer (NaN)
    alias init = nan;

    /// Positive infinity value
    static Binary32 infinity() pure nothrow @nogc @safe @property
    out (r)
    {
        assert(r.isInfinity);
    }
    do
    {
        return Binary32(0, 0xFF, 0);
    }

    /// NaN value
    static Binary32 nan() pure nothrow @nogc @safe @property
    out (r)
    {
        assert(r.isNaN);
    }
    do
    {
        return Binary32(0, 0xFF, (1U << fractionBits) - 1);
    }

    /// Number of decimal digits of precision
    enum int dig = 6; // floor(fractionBits * log_10(2))

    /// Smallest increment to the value 1
    static Binary32 epsilon() pure nothrow @nogc @safe @property
    {
        // 2^-fractionBits
        return Binary32(0, bias - fractionBits, 0);
    }

    /// Number of bits in mantissa
    enum int mant_dig = fractionBits + 1;

    /// Maximum int value such that 2<sup>max_exp-1</sup> is representable
    enum int max_exp = 1 + bias;

    /// Minimum int value such that 2<sup>min_exp-1</sup> is representable as a normalized value
    enum int min_exp = 2 - bias;

    /// Largest representable value that's not infinity
    static Binary32 max() pure nothrow @nogc @safe @property
    out (r)
    {
        assert(r.isFinite);
    }
    do
    {
        // (1-2^-mant_dig) * 2^max_exp
        return Binary32(0, 0xFE, (1U << fractionBits) - 1);
    }

    /// Smallest representable normalized value that's not 0
    static Binary32 min_normal() pure nothrow @nogc @safe @property
    out (r)
    {
        assert(r.isNormal);
    }
    do
    {
        // 2^(min_exp-1)
        return Binary32(0, 1, 0);
    }

    /// Positive 0 value
    static Binary32 zero() pure nothrow @nogc @safe @property
    out (r)
    {
        assert(r.isZero);
    }
    do
    {
        return Binary32(0, 0, 0);
    }

    ///
    Binary32 opUnary(string op)() const if (op == "+" || op == "-")
    {
        static if (op == "+")
        {
            return this;
        }
        else
        {
            Binary32 r = this;
            r.sign = !r.sign;
            return r;
        }
    }

    ///
    @safe pure nothrow @nogc unittest
    {
        immutable a = Binary32(3.14);
        immutable b = Binary32(-3.14);

        assert(+a == a);
        assert(+b == b);
        assert(-a == b);
        assert(-b == a);
    }

    ///
    Binary32 opBinary(string op)(Binary32 rhs) const if (op == "+" || op == "-")
    {
        immutable lhs = this;
        static if (op == "-")
        {
            rhs.sign = !rhs.sign;
        }

        if (lhs.isNaN)
        {
            return lhs;
        }

        if (rhs.isNaN)
        {
            return rhs;
        }

        if (lhs.isInfinity && rhs.isInfinity)
        {
            if (lhs.sign == rhs.sign)
            {
                return lhs.sign ? -infinity : infinity;
            }
            return -nan; // Why -???
        }

        if (lhs.isInfinity)
        {
            return lhs;
        }

        if (rhs.isInfinity)
        {
            return rhs;
        }

        if (lhs.isZero && rhs.isZero)
        {
            return lhs.sign && rhs.sign ? -zero : zero;
        }

        if (lhs.isZero)
        {
            return rhs;
        }

        if (rhs.isZero)
        {
            return lhs;
        }

        immutable lhsMagnitude = (lhs.exponent << fractionBits) | lhs.fraction;
        immutable rhsMagnitude = (rhs.exponent << fractionBits) | rhs.fraction;

        if (lhs.sign != rhs.sign && lhsMagnitude == rhsMagnitude)
        {
            return zero;
        }

        immutable larger = lhsMagnitude > rhsMagnitude ? lhs : rhs;
        immutable smaller = larger == lhs ? rhs : lhs;

        int largerExponent = larger.exponent;
        int smallerExponent = smaller.exponent;

        // [padding][integer: 1].[fraction: fractionBits][GRS: 3]
        uint largerMantissa, smallerMantissa;

        enum implicitLeadingBit = 1U << fractionBits;
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

    ///
    @safe pure nothrow @nogc unittest
    {
        assert(isIdentical(Binary32(-1.0) + Binary32(1.0), Binary32.zero));

        assert(isNaN(Binary32.nan + Binary32(1.0)));
        assert(isNaN(Binary32(1.0) - Binary32.nan));
        assert(isNaN(Binary32.infinity - Binary32.infinity));
        assert(Binary32.infinity + Binary32.infinity == Binary32.infinity);
        assert(Binary32.infinity - Binary32(1.0) == Binary32.infinity);
        assert(Binary32(1.0) - Binary32.infinity == -Binary32.infinity);

        assert(isIdentical(Binary32.zero + Binary32.zero, Binary32.zero));
        assert(isIdentical(Binary32.zero - Binary32.zero, Binary32.zero));
        assert(isIdentical(-Binary32.zero + Binary32.zero, Binary32.zero));
        assert(isIdentical(-Binary32.zero - Binary32.zero, -Binary32.zero));

        assert(Binary32(1.0) - Binary32.zero == Binary32(1.0));
        assert(Binary32.zero - Binary32(1.0) == Binary32(-1.0));

        assert(Binary32(7.0) + Binary32(3.0) == Binary32(7.0 + 3.0));

        assert(Binary32(float.min_normal / 2) + Binary32(
                float.min_normal / 8) == Binary32(float.min_normal / 2 + float.min_normal / 8));
    }

    ///
    Binary32 opBinary(string op)(Binary32 rhs) const if (op == "*")
    {
        immutable lhs = this;
        if (lhs.isNaN)
        {
            return lhs;
        }

        if (rhs.isNaN)
        {
            return rhs;
        }

        if ((lhs.isZero && rhs.isInfinity) || (lhs.isInfinity && rhs.isZero))
        {
            return -nan; // Why -???
        }

        immutable prodSign = lhs.sign ^ rhs.sign;

        if (lhs.isZero || rhs.isZero)
        {
            auto z = zero;
            z.sign = prodSign;
            return z;
        }

        if (lhs.isInfinity || rhs.isInfinity)
        {
            auto inf = infinity;
            inf.sign = prodSign;
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

            enum integerBit = 1U << fractionBits;
            enum fracMask = integerBit - 1;
            foreach (_; 0 .. fractionBits)
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

        int prodExponent = lhsExponent + rhsExponent - cast(int) bias;

        enum implicitLeadingBit = 1UL << fractionBits;
        immutable ulong lhsMantissa = implicitLeadingBit | lhsFraction;
        immutable ulong rhsMantissa = implicitLeadingBit | rhsFraction;

        // [padding][integer: 2].[fraction: fractionBits][extra: fractionBits]
        ulong prodMantissa = lhsMantissa * rhsMantissa;
        foreach (_; 0 .. fractionBits - 3)
        {
            immutable stickyBit = prodMantissa & 1;
            prodMantissa >>>= 1;
            prodMantissa |= stickyBit;
        }
        // [padding][integer: 2].[fraction: fractionBits][GRS: 3]

        return _rounder(prodSign, prodExponent, cast(uint) prodMantissa);
    }

    ///
    @safe pure nothrow @nogc unittest
    {
        assert(isNaN(Binary32.nan * Binary32(1.0)));
        assert(isNaN(Binary32(1.0) * Binary32.nan));

        assert(isNaN(Binary32.infinity * Binary32.zero));

        assert(Binary32.infinity * -Binary32.infinity == -Binary32.infinity);

        assert(isIdentical(Binary32.zero * Binary32(-1.0), -Binary32.zero));

        assert(Binary32(3.14) * Binary32(-1.0) == -Binary32(3.14));
        assert(Binary32(3.14) * Binary32(2.72) == Binary32(3.14f * 2.72f));
        assert(Binary32(float.min_normal / 4) * Binary32(-1.0) == -Binary32(float.min_normal / 4));

        // overflow
        assert(Binary32(2.0) * Binary32.max == Binary32.infinity);

        // underflow
        assert(isIdentical(Binary32(float.min_normal) * -Binary32(float.min_normal / 2),
                -Binary32.zero));

        // overflow after rounding
        assert(Binary32(0x1.46f6d8p+125) * Binary32(0x1.90e02ap+2) == Binary32.infinity);
    }

    ///
    Binary32 opBinary(string op)(Binary32 rhs) const if (op == "/")
    {
        immutable lhs = this;
        if (lhs.isNaN)
        {
            return lhs;
        }

        if (rhs.isNaN)
        {
            return rhs;
        }

        if ((lhs.isZero && rhs.isZero) || (lhs.isInfinity && rhs.isInfinity))
        {
            return -nan; // Why -???
        }

        immutable quotSign = lhs.sign ^ rhs.sign;

        if (lhs.isZero || rhs.isInfinity)
        {
            auto z = zero;
            z.sign = quotSign;
            return z;
        }

        if (lhs.isInfinity || rhs.isZero)
        {
            auto inf = infinity;
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

            enum integerBit = 1U << fractionBits;
            enum fracMask = integerBit - 1;
            foreach (_; 0 .. fractionBits)
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

        immutable quotExponent = lhsExponent - rhsExponent + bias;

        enum implicitLeadingBit = 1U << fractionBits;
        immutable lhsMantissa = implicitLeadingBit | lhsFraction;
        immutable rhsMantissa = implicitLeadingBit | rhsFraction;

        // [padding][integer: 1].[fraction: fractionBits][margin: fractionBits][margin for GRS: 3]
        immutable dividend = cast(ulong) lhsMantissa << (fractionBits + 3);

        // [padding][integer: 1].[fraction: fractionBits][GRS: 3]
        ulong quotMantissa = dividend / rhsMantissa;

        immutable stickyBit = dividend != quotMantissa * rhsMantissa;
        quotMantissa |= stickyBit;
        assert(quotMantissa >>> (fractionBits - 1 + 3));

        return _rounder(quotSign, quotExponent, cast(uint) quotMantissa);
    }

    ///
    @safe pure nothrow @nogc unittest
    {
        assert(isNaN(Binary32.nan / Binary32(2.0)));
        assert(isNaN(Binary32(2.0) / Binary32.nan));

        assert(isNaN(Binary32.zero / Binary32.zero));
        assert(isNaN(Binary32.infinity / Binary32.infinity));
        assert(Binary32.infinity / Binary32(1.0) == Binary32.infinity);
        assert(Binary32.infinity / -Binary32.zero == -Binary32.infinity);

        assert(isIdentical(Binary32(2.0) / -Binary32.infinity, -Binary32.zero));
        assert(Binary32(5.0) / Binary32(3.0) == Binary32(5.0f / 3.0f));

        // overflow
        assert(Binary32.max / Binary32(float.min_normal / 6) == Binary32.infinity);

        // underflow
        assert(isIdentical(Binary32(float.min_normal / 6) / -Binary32.max, -Binary32.zero));
    }

    ///
    Binary32 opOpAssign(string op)(Binary32 rhs)
            if (op == "+" || op == "-" || op == "*" || op == "/")
    {
        this = opBinary!op(rhs);
        return this;
    }

    @safe pure nothrow @nogc unittest
    {
        auto a = Binary32(4.0);
        auto b = Binary32(2.0);
        b += b;
        assert(b == a);
        a -= b;
        assert(a.isZero);
        b *= a;
        assert(b.isZero);
        a /= b;
        assert(a.isNaN);
    }

    ///
    bool opEquals()(auto ref const Binary32 x) const pure nothrow @nogc @safe
    {
        if (this.isZero && x.isZero)
        {
            return true;
        }

        if (this.isNaN || x.isNaN)
        {
            return false;
        }

        return this is x;
    }

    pure nothrow @nogc @safe unittest
    {
        immutable a = Binary32(3.14);
        immutable b = Binary32(-3.14);

        assert(a == a);
        assert(a != b);
        assert(Binary32.zero == -Binary32.zero);
        assert(Binary32.nan != Binary32.nan);
    }

    ///
    string toString() const pure @safe
    {
        import std.format : format;

        immutable fmt = format!"sgn: %%0%sb, exp: %%0%sb, frac: %%0%sb"(signBits,
                exponentBits, fractionBits);
        return format!fmt(sign, exponent, fraction);
    }

    import std.format : FormatSpec;

    ///
    void toString(scope void delegate(const(char)[]) sink, FormatSpec!char fmt) const
    {
        import std.array : appender;

        auto result = appender!string;

        if (fmt.spec == 'A' || fmt.spec == 'a')
        {
            if (sign)
            {
                result ~= '-';
            }
            else if (fmt.flPlus)
            {
                result ~= '+';
            }
            else if (fmt.flSpace)
            {
                result ~= ' ';
            }

            if (isNaN(this) || isInfinity(this))
            {
                result ~= isNaN(this) ? "nan" : "inf";

                if (fmt.flDash && fmt.width > result.data.length)
                {
                    import std.range : repeat;

                    result ~= repeat(' ', fmt.width - result.data.length);
                }
            }
            else
            {
                immutable integerPart = isNormal(this) ? 1U << fractionBits : 0;
                auto mantissa = (integerPart | fraction) << 3;

                immutable resultFractionBits = fmt.precision < 6 ? fmt.precision * 4 : fractionBits;

                mantissa = roundImpl(sign, mantissa, resultFractionBits);

                immutable roundedInt = mantissa >>> fractionBits + 3;
                enum fractionMask = (1U << fractionBits + 3) - 1;
                immutable roundedFrac24 = (mantissa & fractionMask) >> 2;

                immutable hexPrefix = "0x";
                immutable point = ".";

                import std.algorithm : stripRight;
                import std.conv : toChars;
                import std.format : format;
                import std.range : chain, repeat, takeExactly;

                auto hexInt = toChars!16(roundedInt);
                auto hexFracShortest = format!"%06x"(roundedFrac24).stripRight('0');

                immutable hexFracDesiredLength = fmt.precision == fmt.UNSPECIFIED
                    ? hexFracShortest.length : fmt.precision;

                result ~= hexPrefix;

                auto result2 = appender!string;
                result2 ~= hexInt;

                if (fmt.flHash || hexFracDesiredLength)
                {
                    result2 ~= point;
                }

                if (hexFracDesiredLength)
                {
                    result2 ~= hexFracShortest.chain(repeat('0')).takeExactly(hexFracDesiredLength);
                }

                immutable decExp = isNormal(this) ? cast(int) exponent - int(bias) : isSubnormal(this)
                    ? 1 - int(bias) : 0;
                result2 ~= format!"p%+d"(decExp);

                immutable currentLength = result.data.length + result2.data.length;
                if (fmt.width > currentLength)
                {
                    if (fmt.flDash)
                    {
                        result2 ~= repeat(' ', fmt.width - currentLength);
                    }
                    else if (fmt.flZero)
                    {
                        result ~= repeat('0', fmt.width - currentLength);
                    }
                }

                result ~= result2.data;
            }
        }
        else
        {
            throw new Exception("Unknown format specifier: %" ~ fmt.spec);
        }

        import std.range : put;

        if (fmt.width > result.data.length)
        {
            import std.range : repeat;

            sink.put(repeat(' ', fmt.width - result.data.length));
        }

        if (fmt.spec == 'A')
        {
            import std.uni : toUpper;

            sink.put(result.data.toUpper);

        }
        else
        {
            sink.put(result.data);
        }
    }

    unittest  // TODO: simplify
    {
        import std.random : Mt19937;
        import std.algorithm : map;
        import std.range : take;

        union FloatContainer
        {
            uint i;
            float f;
        }

        auto testcases = Mt19937().map!(a => FloatContainer(a).f)
            .map!(a => Binary32(a));

        foreach (a; testcases.take(1000))
        {
            import std.format : format;

            immutable fmts = [
                "% 1a", "%a", "%+.5a", "%.4a", "% -.3a", "%+ .2a", "%.1a",
                "%-#010.0a", "%#A", "%03.7a", "%-17.9a", "%-020a", "%030.a"
            ];
            foreach (fmt; fmts)
            {
                assert(format(fmt, a) == format(fmt, a.value),
                        fmt ~ "@@" ~ format(fmt, a) ~ "@@" ~ format(fmt, a.value));
            }
        }
    }
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

// TODO: Implement more rounding rules
private uint roundImpl(bool sign, uint q26, uint resultFractionBits) pure nothrow @nogc @safe
in
{
    assert(resultFractionBits <= Binary32.fractionBits);
}
out (r)
{
    immutable shift = Binary32.fractionBits - resultFractionBits;
    assert((r >>> shift) << shift == r);
}
do
{
    import std.math : FloatingPointControl;

    switch (FloatingPointControl.rounding)
    {
    case FloatingPointControl.roundToNearest:
        immutable shift = Binary32.fractionBits - resultFractionBits;

        immutable ulp_r_s = q26 & ((0b1011 << shift) | ((1U << shift) - 1));
        immutable g = q26 & (0b100 << shift);
        immutable roundToInf = g && ulp_r_s; // something magic
        q26 >>>= 3 + shift;
        q26 += roundToInf;
        q26 <<= 3 + shift;
        break;
    case FloatingPointControl.roundDown:
        assert(0);
    case FloatingPointControl.roundUp:
        assert(0);
    case FloatingPointControl.roundToZero:
        assert(0);
    default:
        assert(0);
    }
    return q26;
}

nothrow @nogc @safe unittest
{
    import std.math : FloatingPointControl;

    pragma(inline, false);
    FloatingPointControl fpctrl;

    {
        fpctrl.rounding = FloatingPointControl.roundToNearest;

        assert(roundImpl(0, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl(0, 0b10_10100, Binary32.fractionBits - 2) == 0b11_00000);
        assert(roundImpl(0, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl(0, 0b11_100, Binary32.fractionBits) == 0b100_000);

        assert(roundImpl(1, 0b10_0100, Binary32.fractionBits - 1) == 0b10_0000);
        assert(roundImpl(1, 0b10_10100, Binary32.fractionBits - 2) == 0b11_00000);
        assert(roundImpl(1, 0b10_100000, Binary32.fractionBits - 3) == 0b10_000000);
        assert(roundImpl(1, 0b11_100, Binary32.fractionBits) == 0b100_000);
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
