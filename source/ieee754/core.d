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

    private struct _RounderImpl
    {
        bool sign;
        int exponent;
        uint mantissa; // [padding][reserved for carry: 1][integer: 1].[fraction: fractionBits][GRS: 3]

        // param mantissa: [padding][reserved for carry: 1][integer: 1].[fraction: fractionBits][GRS: 3]
        this(bool sign, int exponent, uint mantissa) nothrow @nogc @safe
        {
            this.sign = sign;

            immutable integer = mantissa >>> (fractionBits + 3);

            // Normalize temporarily
            if (integer > 1)
            {
                shiftMantissaToLeftBy1(exponent, mantissa);
            }
            else if (!integer)
            {
                enum integerBit = 1U << (fractionBits + 3);

                foreach (_; 0 .. fractionBits + 3)
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

        void shiftMantissaToLeftBy1(ref int exp, ref uint mant) nothrow @nogc @safe
        {
            immutable stickyBit = mant & 1;
            exp++;
            mant >>>= 1;
            mant |= stickyBit;
        }

        uint integerPart() const pure nothrow @nogc @safe @property
        {
            return mantissa >>> (fractionBits + 3);
        }

        uint fractionPart() const pure nothrow @nogc @safe @property
        {
            enum fracMask = (1 << fractionBits) - 1;
            return (mantissa >>> 3) & fracMask;
        }

        void round() nothrow @nogc @safe // round to nearest even (RN)
        {
            immutable ulp_r_s = mantissa & 0b1011;
            immutable g = mantissa & 0b100;
            immutable roundUp = g && ulp_r_s; // something magic
            mantissa >>>= 3;
            mantissa += roundUp;
            mantissa <<= 3;

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
                return sign ? -infinity : infinity;
            }
            assert(exponent < 0xFF);
            assert(exponent > 0);

            return Binary32(sign, underflow ? 0 : cast(ubyte) exponent, fractionPart);
        }

        string toString() const pure @safe
        {
            import std.format : format;

            immutable fmt = format!"exp: %%0%sb, int: %%0%sb, frac: %%0%sb, grs: %%0%sb"(exponentBits,
                    2, fractionBits, 3);
            return format!fmt(exponent, integerPart, fractionPart, mantissa & 0b111);
        }
    }

    private Binary32 _rounder(bool sign, int exponent, uint mantissa) const nothrow @nogc @safe
    {
        auto r = _RounderImpl(sign, exponent, mantissa);

        if (r.overflow) // unrecoverable
        {
            return r.result;
        }

        r.round();
        return r.result;
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
    string toString() const pure @safe
    {
        import std.format : format;

        immutable fmt = format!"sgn: %%0%sb, exp: %%0%sb, frac: %%0%sb"(signBits,
                exponentBits, fractionBits);
        return format!fmt(sign, exponent, fraction);
    }
}

unittest
{
    auto a = Binary32(3.14);
    auto b = Binary32(-3.14);

    assert((+a).value == a.value);
    assert((+b).value == b.value);
    assert((-a).value == b.value);
    assert((-b).value == a.value);
}

unittest
{
    import std.random : Mt19937;
    import std.algorithm : map;
    import std.range : slide, take;

    union FloatContainer
    {
        uint i;
        float f;
    }

    auto testcases = Mt19937(17).map!(a => FloatContainer(a).f)
        .map!(a => Binary32(a))
        .slide(2);

    foreach (operands; testcases.take(1000))
    {
        immutable lhs = operands.front;
        operands.popFront();
        immutable rhs = operands.front;

        immutable sum = lhs + rhs;
        immutable sumRef = Binary32(lhs.value + rhs.value);

        if (sum.isNaN)
        {
            assert(sumRef.isNaN);
        }
        else
        {
            import std.format : format;

            assert(sum.value == sumRef.value, format!"%a + %a = %a, %a"(lhs.value,
                    rhs.value, sum.value, sumRef.value) ~ "\n" ~ format!"%s\n%s\n%s\n%s"(lhs,
                    rhs, sum, sumRef));
        }
    }
}

unittest
{
    import std.random : Mt19937;
    import std.algorithm : map;
    import std.range : slide, take;

    union FloatContainer
    {
        uint i;
        float f;
    }

    auto testcases = Mt19937(9).map!(a => FloatContainer(a).f)
        .map!(a => Binary32(a))
        .slide(2);

    foreach (operands; testcases.take(1000))
    {
        immutable lhs = operands.front;
        operands.popFront();
        immutable rhs = operands.front;

        immutable diff = lhs - rhs;
        immutable diffRef = Binary32(lhs.value - rhs.value);

        if (diff.isNaN)
        {
            assert(diffRef.isNaN);
        }
        else
        {
            import std.format : format;

            assert(diff.value == diffRef.value, format!"%a - %a = %a, %a"(lhs.value,
                    rhs.value, diff.value, diffRef.value) ~ "\n" ~ format!"%s\n%s\n%s\n%s"(lhs,
                    rhs, diff, diffRef));
        }
    }
}

unittest
{
    import std.random : Mt19937;
    import std.algorithm : map;
    import std.range : slide, take;

    union FloatContainer
    {
        uint i;
        float f;
    }

    auto testcases = Mt19937().map!(a => FloatContainer(a).f)
        .map!(a => Binary32(a))
        .slide(2);

    foreach (operands; testcases.take(1000))
    {
        immutable lhs = operands.front;
        operands.popFront();
        immutable rhs = operands.front;

        immutable prod = lhs * rhs;
        immutable prodRef = Binary32(lhs.value * rhs.value);

        if (prod.isNaN)
        {
            assert(prodRef.isNaN);
        }
        else
        {
            import std.format : format;

            assert(prod.value == prodRef.value, format!"%a * %a = %a, %a"(lhs.value,
                    rhs.value, prod.value, prodRef.value));
        }
    }
}

unittest
{
    import std.random : Mt19937;
    import std.algorithm : map;
    import std.range : slide, take;

    union FloatContainer
    {
        uint i;
        float f;
    }

    auto testcases = Mt19937().map!(a => FloatContainer(a).f)
        .map!(a => Binary32(a))
        .slide(2);

    foreach (operands; testcases.take(1000))
    {
        immutable lhs = operands.front;
        operands.popFront();
        immutable rhs = operands.front;

        immutable quot = lhs / rhs;
        immutable quotRef = Binary32(lhs.value / rhs.value);

        if (quot.isNaN)
        {
            assert(quotRef.isNaN);
        }
        else
        {
            import std.format : format;

            assert(quot.value == quotRef.value, format!"%a / %a = %a, %a"(lhs.value,
                    rhs.value, quot.value, quotRef.value));
        }
    }
}

unittest
{
    assert((Binary32.zero * Binary32.infinity).isNaN);
    auto f = Binary32(-11.2);
    assert((Binary32.zero * f).isZero);
    assert((f * Binary32.infinity).isInfinity);
}

// Overflow after rounding
unittest
{
    auto f = Binary32(0x1.46f6d8p+125);
    auto g = Binary32(0x1.90e02ap+2);
    assert((f * g).isInfinity);
}
