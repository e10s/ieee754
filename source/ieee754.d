module ieee754;

/// Single precision FP
struct Binary32
{
    import std.bitmanip : bitfields;

    // borrowed from std_bitmanip.FloatRep
    union
    {
        float value;
        mixin(bitfields!(uint, "fraction", 23, ubyte, "exponent", 8, bool, "sign", 1));
    }

    enum uint bias = 127, fractionBits = 23, exponentBits = 8, signBits = 1;

    string toString() const pure @safe
    {
        import std.format : format;

        immutable fmt = format!"sgn: %%0%sb, exp: %%0%sb, frac: %%0%sb"(signBits,
                exponentBits, fractionBits);
        return format!fmt(sign, exponent, fraction);
    }

    bool isFinite() const pure nothrow @nogc @safe @property
    {
        return exponent != 0xFF;
    }

    bool isInfinity() const pure nothrow @nogc @safe @property
    {
        return exponent == 0xFF && !fraction;
    }

    bool isNaN() const pure nothrow @nogc @safe @property
    {
        return exponent == 0xFF && fraction;
    }

    bool isNormal() const pure nothrow @nogc @safe @property
    {
        return exponent && exponent != 0xFF;
    }
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

    f.exponent = 0;
    f.fraction = 1;
    assert(!f.isNormal);

    f.value = 0;
    assert(!f.isNormal);

    f.value = float.nan;
    assert(!f.isFinite);
    assert(!f.isInfinity);
    assert(f.isNaN);
    assert(!f.isNormal);

    f.value = float.infinity;
    assert(!f.isFinite);
    assert(f.isInfinity);
    f.sign = 1;
    assert(f.isInfinity);
    assert(!f.isNaN);
    assert(!f.isNormal);
}
