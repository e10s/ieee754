module ieee754.type;

import ieee754.core;

/// Single precision FP
alias Binary32 = IEEE754Binary!32;
///
enum bool isIEEE754Binary(T) = is(T == IEEE754Binary!n, alias n);
static assert(isIEEE754Binary!Binary32);

///
mixin template IEEE754Binary32Properties()
{
    ///
    alias SignType = bool;
    ///
    alias ExponentType = ubyte;
    ///
    alias FractionType = uint;
    ///
    alias PrimitiveType = float;

    ///
    enum uint bias = 127, fractionBits = 23, exponentBits = 8, signBits = 1;

    /// Number of decimal digits of precision
    enum int dig = 6; // floor(fractionBits * log_10(2))
}

///
struct IEEE754Binary(uint floatBits) if (floatBits == 32)
{
    mixin IEEE754Binary32Properties;

    import std.bitmanip : bitfields;

    mixin(bitfields!(FractionType, "fraction", fractionBits, ExponentType,
            "exponent", exponentBits, SignType, "sign", signBits));

    ///
    this(PrimitiveType value) pure nothrow @nogc @trusted
    {
        this = *cast(IEEE754Binary*)&value;
    }

    ///
    this(SignType sign, ExponentType exponent, FractionType fraction) pure nothrow @nogc @safe
    {
        this.sign = sign;
        this.exponent = exponent;
        this.fraction = fraction;
    }

    ///
    PrimitiveType value() const pure nothrow @nogc @trusted @property
    {
        return *cast(PrimitiveType*)&this;
    }

    /// Initializer (NaN)
    alias init = nan;

    //-----------------

    /// Positive infinity value
    enum IEEE754Binary infinity = IEEE754Binary(0, max_exp + bias, 0);

    /// NaN value
    enum IEEE754Binary nan = IEEE754Binary(0, max_exp + bias, (FractionType(1) << fractionBits) - 1);

    /// Smallest increment to the value 1
    enum IEEE754Binary epsilon = IEEE754Binary(0, bias - fractionBits, 0); // 2^-fractionBits

    /// Number of bits in mantissa
    enum int mant_dig = fractionBits + 1;

    /// Maximum int value such that 2<sup>max_exp-1</sup> is representable
    enum int max_exp = 1 + bias;

    /// Minimum int value such that 2<sup>min_exp-1</sup> is representable as a normalized value
    enum int min_exp = 2 - bias;

    /// Largest representable value that's not infinity
    enum IEEE754Binary max = IEEE754Binary(0, max_exp - 1 + bias,
                (FractionType(1) << fractionBits) - 1); // (1-2^-mant_dig) * 2^max_exp

    /// Smallest representable normalized value that's not 0
    enum IEEE754Binary min_normal = IEEE754Binary(0, 1, 0); // 2^(min_exp-1)

    /// Positive 0 value
    enum IEEE754Binary zero = IEEE754Binary(0, 0, 0);

    //-----------------

    ///
    IEEE754Binary opUnary(string op)() const if (op == "+" || op == "-")
    {
        static if (op == "+")
        {
            return this;
        }
        else
        {
            IEEE754Binary r = this;
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
    IEEE754Binary opBinary(string op)(IEEE754Binary rhs) const pure
            if (op == "+" || op == "-")
    {
        immutable lhs = this;

        import ieee754.math : isInfinity, isNaN, isZero;

        static if (op == "-")
        {
            rhs.sign = !rhs.sign;
        }

        if (isNaN(lhs))
        {
            return lhs;
        }

        if (isNaN(rhs))
        {
            return rhs;
        }

        if (isInfinity(lhs) && isInfinity(rhs))
        {
            if (lhs.sign == rhs.sign)
            {
                return lhs.sign ? -infinity : infinity;
            }
            return -nan; // Why -???
        }

        if (isInfinity(lhs))
        {
            return lhs;
        }

        if (isInfinity(rhs))
        {
            return rhs;
        }

        return add(lhs, rhs);
    }

    ///
    @safe pure nothrow @nogc unittest
    {
        import ieee754.math : isIdentical, isNaN;

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
    @safe nothrow @nogc unittest
    {
        import ieee754.math : isIdentical;
        import std.math : FloatingPointControl;

        pragma(inline, false);
        FloatingPointControl fpctrl;
        fpctrl.rounding = FloatingPointControl.roundDown;
        assert(isIdentical(Binary32(-1.0) + Binary32(1.0), -Binary32.zero));
        assert(isIdentical(Binary32.zero - Binary32.zero, -Binary32.zero));
        assert(isIdentical(-Binary32.zero + Binary32.zero, -Binary32.zero));
    }

    ///
    IEEE754Binary opBinary(string op)(IEEE754Binary rhs) const if (op == "*")
    {
        immutable lhs = this;

        import ieee754.math : isInfinity, isNaN, isZero;

        if (isNaN(lhs))
        {
            return lhs;
        }

        if (isNaN(rhs))
        {
            return rhs;
        }

        if ((isZero(lhs) && isInfinity(rhs)) || (isInfinity(lhs) && isZero(rhs)))
        {
            return -nan; // Why -???
        }

        if (lhs.isInfinity || rhs.isInfinity)
        {
            auto inf = infinity;
            inf.sign = lhs.sign ^ rhs.sign;
            return inf;
        }

        return mul(lhs, rhs);
    }

    ///
    @safe pure nothrow @nogc unittest
    {
        import ieee754.math : isIdentical, isNaN;

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
    IEEE754Binary opBinary(string op)(IEEE754Binary rhs) const pure nothrow @nogc @safe
            if (op == "/")
    {
        immutable lhs = this;

        import ieee754.math : isInfinity, isNaN, isZero;

        if (isNaN(lhs))
        {
            return lhs;
        }

        if (isNaN(rhs))
        {
            return rhs;
        }

        if ((isZero(lhs) && isZero(rhs)) || (isInfinity(lhs) && isInfinity(rhs)))
        {
            return -nan; // Why -???
        }

        if (isZero(lhs) || isInfinity(rhs))
        {
            auto z = zero;
            z.sign = lhs.sign ^ rhs.sign;
            return z;
        }

        if (isInfinity(lhs) || isZero(rhs))
        {
            auto inf = infinity;
            inf.sign = lhs.sign ^ rhs.sign;
            return inf;
        }

        return div(lhs, rhs);
    }

    ///
    @safe pure nothrow @nogc unittest
    {
        import ieee754.math : isIdentical, isNaN;

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
    IEEE754Binary opOpAssign(string op)(IEEE754Binary rhs)
            if (op == "+" || op == "-" || op == "*" || op == "/")
    {
        this = opBinary!op(rhs);
        return this;
    }

    @safe pure nothrow @nogc unittest
    {
        import ieee754.math : isNaN, isZero;

        auto a = Binary32(4.0);
        auto b = Binary32(2.0);
        b += b;
        assert(b == a);
        a -= b;
        assert(isZero(a));
        b *= a;
        assert(isZero(b));
        a /= b;
        assert(isNaN(a));
    }

    ///
    bool opEquals()(auto ref const IEEE754Binary x) const pure nothrow @nogc @safe
    {
        import ieee754.math : isNaN, isZero;

        if (isZero(this) && isZero(x))
        {
            return true;
        }

        if (isNaN(this) || isNaN(x))
        {
            return false;
        }

        return this is x;
    }

    ///
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
        import std.range : put;

        if (fmt.spec == 's')
        {
            sink.put(toString());
            return;
        }

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

            import ieee754.math : isInfinity, isNaN;

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
                import ieee754.math : isNormal, isSubnormal;

                immutable integerPart = isNormal(this) ? FractionType(1) << fractionBits : 0;
                auto mantissa = (integerPart | fraction) << 3;

                immutable resultFractionBits = fmt.precision < 6 ? fmt.precision * 4 : fractionBits;

                import ieee754.core : roundImpl;

                mantissa = roundImpl!IEEE754Binary(sign, mantissa, resultFractionBits);

                immutable roundedInt = mantissa >>> fractionBits + 3;
                enum fractionMask = (FractionType(1) << fractionBits + 3) - 1;
                immutable roundedFracWithOneMoreBit = (mantissa & fractionMask) >> 2;

                immutable hexPrefix = "0x";
                immutable point = ".";

                import std.algorithm : stripRight;
                import std.conv : toChars;
                import std.format : format;
                import std.range : chain, repeat, takeExactly;

                auto hexInt = toChars!16(roundedInt);
                auto hexFracShortest = format!"%06x"(roundedFracWithOneMoreBit).stripRight('0');

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
