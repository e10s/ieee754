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
        Binary32 inf;
        inf.sign = 0;
        inf.exponent = 0xFF;
        inf.fraction = 0;
        return inf;
    }

    /// NaN value
    static Binary32 nan() pure nothrow @nogc @safe @property
    out (r)
    {
        assert(r.isNaN);
    }
    do
    {
        Binary32 nan;
        nan.sign = 0;
        nan.exponent = 0xFF;
        nan.fraction = 1 << fractionBits - 1;
        return nan;
    }

    /// Number of decimal digits of precision
    enum int dig = 6; // floor(fractionBits * log_10(2))

    /// Smallest increment to the value 1
    static Binary32 epsilon() pure nothrow @nogc @safe @property
    {
        // 2^-fractionBits
        Binary32 eps;
        eps.sign = 0;
        eps.exponent = bias - fractionBits;
        eps.fraction = 0;
        return eps;
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
        Binary32 maxFinite;
        maxFinite.sign = 0;
        maxFinite.exponent = 0xFE;
        maxFinite.fraction = (1U << fractionBits) - 1;
        return maxFinite;
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
        Binary32 minNormal;
        minNormal.sign = 0;
        minNormal.exponent = 1;
        minNormal.fraction = 0;
        return minNormal;
    }

    /// Positive 0 value
    static Binary32 zero() pure nothrow @nogc @safe @property
    out (r)
    {
        assert(r.isZero);
    }
    do
    {
        Binary32 zero;
        zero.sign = 0;
        zero.exponent = 0;
        zero.fraction = 0;
        return zero;
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
            auto NaN = nan;
            NaN.sign = 1; // ???
            return NaN;
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

        Binary32 ret;
        ret.sign = prodSign;
        ret.exponent = prod.underflow ? 0 : cast(ubyte) prod.exponent;
        ret.fraction = prod.fractionPart;
        return ret;
    }

    ///
    string toString() const pure @safe
    {
        import std.format : format;

        immutable fmt = format!"sgn: %%0%sb, exp: %%0%sb, frac: %%0%sb"(signBits,
                exponentBits, fractionBits);
        return format!fmt(sign, exponent, fraction);
    }

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
    Binary32 a = {value: 3.14};
    Binary32 b = {value: -3.14};

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

    auto testcases = Mt19937().map!(a => FloatContainer(a).f)
        .map!(a => { Binary32 b = {value: a}; return b; }())
        .slide(2);

    foreach (operands; testcases.take(1000))
    {
        immutable lhs = operands.front;
        operands.popFront();
        immutable rhs = operands.front;

        immutable prod = lhs * rhs;
        immutable Binary32 prodRef = {value: lhs.value * rhs.value};

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
    Binary32 f;
    f.value = -11.2;
    assert((Binary32.zero * f).isZero);
    assert((f * Binary32.infinity).isInfinity);
}

// Overflow after rounding
unittest
{
    Binary32 f, g;
    f.value = 0x1.46f6d8p+125;
    g.value = 0x1.90e02ap+2;
    assert((f * g).isInfinity);
}

unittest
{
    Binary32 f;
    f.sign = 1;
    f.exponent = 0b01111100;
    f.fraction = 0b010_0000_0000_0000_0000_0000;
    assert(f.value == -.15625);
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

    f.value = 128;
    assert(f.isPowerOf2);

    f.value = 0;
    assert(!f.isNormal);
    assert(!f.isPowerOf2);
    assert(!f.isSubnormal);

    f.value = float.nan;
    assert(!f.isFinite);
    assert(!f.isInfinity);
    assert(f.isNaN);
    assert(!f.isNormal);
    assert(!f.isPowerOf2);
    assert(!f.isSubnormal);

    f.value = float.infinity;
    assert(!f.isFinite);
    assert(f.isInfinity);
    assert(!f.isPowerOf2);
    f.sign = 1;
    assert(f.isInfinity);
    assert(!f.isNaN);
    assert(!f.isNormal);
    assert(!f.isSubnormal);
}
