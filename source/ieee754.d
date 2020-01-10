module ieee754;

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
    this(float value)
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

    private struct Rounder // TODO: use this in opMul
    {
        bool sign;
        int exponent;
        uint mantissa; // [padding][reserved for carry: 1][integer: 1].[fraction: fractionBits][GRS: 3]

        // param mantissa: [padding][reserved for carry: 1][integer: 1].[fraction: fractionBits][GRS: 3]
        this(bool sign, int exponent, uint mantissa)
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

                foreach (i; 0 .. fractionBits + 3)
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

        void shiftMantissaToLeftBy1(ref int exp, ref uint mant)
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

        void round() // round to nearest even (RN)
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

    ///
    Binary32 opBinary(string op)(Binary32 rhs) const if (op == "+" || op == "-")
    {
        immutable lhs = this;
        if (op == "-")
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

        auto sum = Rounder(sumSign, cast(ubyte) sumExponent, sumMantissa);

        if (sum.overflow) // unrecoverable
        {
            return sum.result;
        }

        sum.round();

        return sum.result;
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
        void normalizeSubnormal(ref int exp, ref uint frac)
        in
        {
            assert(!exp); // Exponent of subnormal is 0
        }
        do
        {
            exp = 1;
            foreach (i; 1 .. fractionBits + 1)
            {
                enum implicitLeadingBit = 1U << fractionBits;
                enum fracMask = implicitLeadingBit - 1;
                if ((frac << i) & implicitLeadingBit)
                {
                    exp -= i;
                    frac = (frac << i) & fracMask;

                    break;
                }
            }
        }

        if (!lhsExponent) // lhs is subnormal
        {
            normalizeSubnormal(lhsExponent, lhsFraction);
        }

        if (!rhsExponent) // rhs is subnormal
        {
            normalizeSubnormal(rhsExponent, rhsFraction);
        }

        struct Product
        {
            bool sign; // for future use
            int exponent;
            uint mantissa; // [padding][reserved for carry: 1][integer: 1].[fraction: fractionBits][GRS: 3]

            // param mantissa: [padding][integer: 2].[fraction: fractionBits][extra: fractionBits]
            this(bool sign, int exponent, ulong mantissa)
            {
                this.sign = sign;

                bool stickyBit;

                immutable integer = mantissa >>> (fractionBits * 2);
                if (integer > 1) // Normalize
                {
                    stickyBit = mantissa & 1;
                    exponent++;
                    mantissa >>>= 1;
                }

                if (exponent < 1) // Subnormalize
                {
                    // Make 0.xxxx * 2^1
                    immutable shift = 1 - exponent;
                    foreach (_; 0 .. shift)
                    {
                        stickyBit |= mantissa & 1;
                        exponent++;
                        mantissa >>>= 1;
                    }
                    assert(exponent == 1);
                }

                this.exponent = exponent;

                // Now, mantissa means: [padding][integer: 1].[fraction: fractionBits][GR: 2][tmp S: 1][extra for S: fractionBits-3]
                enum extraBits = fractionBits - 3;
                enum extraMask = (1 << extraBits) - 1;
                stickyBit |= cast(bool)(mantissa & extraMask);
                this.mantissa = cast(uint)(mantissa >>> extraBits) | stickyBit;
            }

            uint integerPart() const @property
            {
                return mantissa >>> (fractionBits + 3);
            }

            uint fractionPart() const @property
            {
                enum fracMask = (1 << fractionBits) - 1;
                return (mantissa >>> 3) & fracMask;
            }

            void round() // round to nearest even (RN)
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
                    exponent += 1;
                    immutable stickyBit = mantissa & 1;
                    mantissa >>>= 1;
                    mantissa |= stickyBit;
                }
            }

            bool overflow() const @property
            {
                return exponent > 0xFE;
            }

            bool underflow() const @property
            {
                return exponent <= 1 && !integerPart;
            }
            // DEBUG
            string toString() const pure @safe
            {
                import std.format : format;

                immutable fmt = format!"exp: %%0%sb, int: %%0%sb, frac: %%0%sb, grs: %%0%sb"(exponentBits,
                        2, fractionBits, 3);
                return format!fmt(exponent, integerPart, fractionPart, mantissa & 0b111);
            }
        }

        enum implicitLeadingBit = 1UL << fractionBits;
        immutable ulong lhsMantissa = implicitLeadingBit | lhsFraction;
        immutable ulong rhsMantissa = implicitLeadingBit | rhsFraction;

        // [padding][integer: 2].[fraction: fractionBits][extra: fractionBits]
        immutable prodMantissa = lhsMantissa * rhsMantissa;

        auto prod = Product(prodSign, lhsExponent + rhsExponent - cast(int) bias, prodMantissa);

        if (prod.overflow) // unrecoverable
        {
            auto inf = infinity;
            inf.sign = prodSign;
            return inf;
        }

        prod.round();

        if (prod.overflow)
        {
            auto inf = infinity;
            inf.sign = prodSign;
            return inf;
        }

        assert(prod.exponent < 0xFF);
        assert(prod.exponent > 0);

        return Binary32(prodSign, prod.underflow ? 0 : cast(ubyte) prod.exponent, prod.fractionPart);
    }

    ///
    string toString() const pure @safe
    {
        import std.format : format;

        immutable fmt = format!"sgn: %%0%sb, exp: %%0%sb, frac: %%0%sb"(signBits,
                exponentBits, fractionBits);
        return format!fmt(sign, exponent, fraction);
    }

    //---------------------------

    ///
    Binary32 fabs() const pure nothrow @nogc @safe @property
    {
        return sign ? Binary32(0, exponent, fraction) : this;
    }

    //---------------------------

    ///
    bool isFinite() const pure nothrow @nogc @safe @property
    {
        return exponent != 0xFF;
    }

    ///
    bool isInfinity() const pure nothrow @nogc @safe @property
    {
        return exponent == 0xFF && !fraction;
    }

    ///
    bool isNaN() const pure nothrow @nogc @safe @property
    {
        return exponent == 0xFF && fraction;
    }

    ///
    bool isNormal() const pure nothrow @nogc @safe @property
    {
        return exponent && exponent != 0xFF;
    }

    ///
    bool isPowerOf2() const pure nothrow @nogc @safe @property
    {
        if (sign)
        {
            return false;
        }

        if (isNormal)
        {
            return !fraction;
        }
        else if (isSubnormal)
        {
            import core.bitop : popcnt;

            return popcnt(fraction) == 1;
        }

        return false;
    }

    ///
    bool isSubnormal() const pure nothrow @nogc @safe @property
    {
        return !exponent && fraction;
    }

    ///
    bool isZero() const pure nothrow @nogc @safe @property
    {
        return !exponent && !fraction;
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
