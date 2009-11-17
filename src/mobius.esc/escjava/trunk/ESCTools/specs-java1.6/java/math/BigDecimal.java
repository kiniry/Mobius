package java.math;

public class BigDecimal extends Number implements Comparable {
    /*synthetic*/ static final boolean $assertionsDisabled = !BigDecimal.class.desiredAssertionStatus();
    private volatile BigInteger intVal;
    private int scale = 0;
    private volatile transient int precision = 0;
    private volatile transient String stringCache = null;
    private static final long INFLATED = Long.MIN_VALUE;
    private transient long intCompact = INFLATED;
    private static final int MAX_COMPACT_DIGITS = 18;
    private static final int MAX_BIGINT_BITS = 62;
    private static final long serialVersionUID = 6108874887143696463L;
    private static final BigDecimal[] zeroThroughTen = {new BigDecimal(BigInteger.ZERO, 0, 0), new BigDecimal(BigInteger.ONE, 1, 0), new BigDecimal(BigInteger.valueOf(2), 2, 0), new BigDecimal(BigInteger.valueOf(3), 3, 0), new BigDecimal(BigInteger.valueOf(4), 4, 0), new BigDecimal(BigInteger.valueOf(5), 5, 0), new BigDecimal(BigInteger.valueOf(6), 6, 0), new BigDecimal(BigInteger.valueOf(7), 7, 0), new BigDecimal(BigInteger.valueOf(8), 8, 0), new BigDecimal(BigInteger.valueOf(9), 9, 0), new BigDecimal(BigInteger.TEN, 10, 0)};
    public static final BigDecimal ZERO = zeroThroughTen[0];
    public static final BigDecimal ONE = zeroThroughTen[1];
    public static final BigDecimal TEN = zeroThroughTen[10];
    
    public BigDecimal(char[] in, int offset, int len) {
        
        try {
            boolean isneg = false;
            if (in[offset] == '-') {
                isneg = true;
                offset++;
                len--;
            } else if (in[offset] == '+') {
                offset++;
                len--;
            }
            int dotoff = -1;
            int cfirst = offset;
            long exp = 0;
            if (len > in.length) throw new NumberFormatException();
            char[] coeff = new char[len];
            char c;
            for (; len > 0; offset++, len--) {
                c = in[offset];
                if ((c >= '0' && c <= '9') || Character.isDigit(c)) {
                    coeff[precision] = c;
                    precision++;
                    continue;
                }
                if (c == '.') {
                    if (dotoff >= 0) throw new NumberFormatException();
                    dotoff = offset;
                    continue;
                }
                if ((c != 'e') && (c != 'E')) throw new NumberFormatException();
                offset++;
                c = in[offset];
                len--;
                boolean negexp = false;
                if (c == '-' || c == '+') {
                    negexp = (c == '-');
                    offset++;
                    c = in[offset];
                    len--;
                }
                if (len <= 0) throw new NumberFormatException();
                while (len > 10 && Character.digit(c, 10) == 0) {
                    offset++;
                    c = in[offset];
                    len--;
                }
                if (len > 10) throw new NumberFormatException();
                for (; ; len--) {
                    int v;
                    if (c >= '0' && c <= '9') {
                        v = c - '0';
                    } else {
                        v = Character.digit(c, 10);
                        if (v < 0) throw new NumberFormatException();
                    }
                    exp = exp * 10 + v;
                    if (len == 1) break;
                    offset++;
                    c = in[offset];
                }
                if (negexp) exp = -exp;
                if ((int)exp != exp) throw new NumberFormatException();
                break;
            }
            if (precision == 0) throw new NumberFormatException();
            if (dotoff >= 0) {
                scale = precision - (dotoff - cfirst);
            }
            if (exp != 0) {
                try {
                    scale = checkScale(-exp + scale);
                } catch (ArithmeticException e) {
                    throw new NumberFormatException("Scale out of range.");
                }
            }
            int first = 0;
            for (; (coeff[first] == '0' || Character.digit(coeff[first], 10) == 0) && precision > 1; first++) precision--;
            char[] quick;
            if (!isneg) {
                quick = new char[precision];
                System.arraycopy(coeff, first, quick, 0, precision);
            } else {
                quick = new char[precision + 1];
                quick[0] = '-';
                System.arraycopy(coeff, first, quick, 1, precision);
            }
            if (precision <= MAX_COMPACT_DIGITS) intCompact = Long.parseLong(new String(quick)); else intVal = new BigInteger(quick);
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new NumberFormatException();
        } catch (NegativeArraySizeException e) {
            throw new NumberFormatException();
        }
    }
    
    public BigDecimal(char[] in, int offset, int len, MathContext mc) {
        this(in, offset, len);
        if (mc.precision > 0) roundThis(mc);
    }
    
    public BigDecimal(char[] in) {
        this(in, 0, in.length);
    }
    
    public BigDecimal(char[] in, MathContext mc) {
        this(in, 0, in.length, mc);
    }
    
    public BigDecimal(String val) {
        this(val.toCharArray(), 0, val.length());
    }
    
    public BigDecimal(String val, MathContext mc) {
        this(val.toCharArray(), 0, val.length());
        if (mc.precision > 0) roundThis(mc);
    }
    
    public BigDecimal(double val) {
        
        if (Double.isInfinite(val) || Double.isNaN(val)) throw new NumberFormatException("Infinite or NaN");
        long valBits = Double.doubleToLongBits(val);
        int sign = ((valBits >> 63) == 0 ? 1 : -1);
        int exponent = (int)((valBits >> 52) & 2047L);
        long significand = (exponent == 0 ? (valBits & ((1L << 52) - 1)) << 1 : (valBits & ((1L << 52) - 1)) | (1L << 52));
        exponent -= 1075;
        if (significand == 0) {
            intVal = BigInteger.ZERO;
            intCompact = 0;
            precision = 1;
            return;
        }
        while ((significand & 1) == 0) {
            significand >>= 1;
            exponent++;
        }
        intVal = BigInteger.valueOf(sign * significand);
        if (exponent < 0) {
            intVal = intVal.multiply(BigInteger.valueOf(5).pow(-exponent));
            scale = -exponent;
        } else if (exponent > 0) {
            intVal = intVal.multiply(BigInteger.valueOf(2).pow(exponent));
        }
        if (intVal.bitLength() <= MAX_BIGINT_BITS) {
            intCompact = intVal.longValue();
        }
    }
    
    public BigDecimal(double val, MathContext mc) {
        this(val);
        if (mc.precision > 0) roundThis(mc);
    }
    
    public BigDecimal(BigInteger val) {
        
        intVal = val;
        if (val.bitLength() <= MAX_BIGINT_BITS) {
            intCompact = val.longValue();
        }
    }
    
    public BigDecimal(BigInteger val, MathContext mc) {
        
        intVal = val;
        if (mc.precision > 0) roundThis(mc);
    }
    
    public BigDecimal(BigInteger unscaledVal, int scale) {
        
        intVal = unscaledVal;
        this.scale = scale;
        if (unscaledVal.bitLength() <= MAX_BIGINT_BITS) {
            intCompact = unscaledVal.longValue();
        }
    }
    
    public BigDecimal(BigInteger unscaledVal, int scale, MathContext mc) {
        
        intVal = unscaledVal;
        this.scale = scale;
        if (mc.precision > 0) roundThis(mc);
    }
    
    public BigDecimal(int val) {
        
        intCompact = val;
    }
    
    public BigDecimal(int val, MathContext mc) {
        
        intCompact = val;
        if (mc.precision > 0) roundThis(mc);
    }
    
    public BigDecimal(long val) {
        
        if (compactLong(val)) intCompact = val; else intVal = BigInteger.valueOf(val);
    }
    
    public BigDecimal(long val, MathContext mc) {
        
        if (compactLong(val)) intCompact = val; else intVal = BigInteger.valueOf(val);
        if (mc.precision > 0) roundThis(mc);
    }
    
    private BigDecimal(long val, int scale) {
        
        this.intCompact = val;
        this.scale = scale;
    }
    
    private BigDecimal(BigInteger intVal, long val, int scale) {
        
        this.intVal = intVal;
        this.intCompact = val;
        this.scale = scale;
    }
    
    public static BigDecimal valueOf(long unscaledVal, int scale) {
        if (scale == 0 && unscaledVal >= 0 && unscaledVal <= 10) {
            return zeroThroughTen[(int)unscaledVal];
        }
        if (compactLong(unscaledVal)) return new BigDecimal(unscaledVal, scale);
        return new BigDecimal(BigInteger.valueOf(unscaledVal), scale);
    }
    
    public static BigDecimal valueOf(long val) {
        return valueOf(val, 0);
    }
    
    public static BigDecimal valueOf(double val) {
        return new BigDecimal(Double.toString(val));
    }
    
    public BigDecimal add(BigDecimal augend) {
        BigDecimal[] arg = {this, augend};
        matchScale(arg);
        long x = arg[0].intCompact;
        long y = arg[1].intCompact;
        if (x != INFLATED && y != INFLATED) {
            long sum = x + y;
            if ((((sum ^ x) & (sum ^ y)) >> 63) == 0L) return BigDecimal.valueOf(sum, arg[0].scale);
        }
        return new BigDecimal(arg[0].inflate().intVal.add(arg[1].inflate().intVal), arg[0].scale);
    }
    
    public BigDecimal add(BigDecimal augend, MathContext mc) {
        if (mc.precision == 0) return add(augend);
        BigDecimal lhs = this;
        this.inflate();
        augend.inflate();
        {
            boolean lhsIsZero = lhs.signum() == 0;
            boolean augendIsZero = augend.signum() == 0;
            if (lhsIsZero || augendIsZero) {
                int preferredScale = Math.max(lhs.scale(), augend.scale());
                BigDecimal result;
                if (lhsIsZero && augendIsZero) return new BigDecimal(BigInteger.ZERO, 0, preferredScale);
                result = lhsIsZero ? augend.doRound(mc) : lhs.doRound(mc);
                if (result.scale() == preferredScale) return result; else if (result.scale() > preferredScale) return new BigDecimal(result.intVal, result.intCompact, result.scale).stripZerosToMatchScale(preferredScale); else {
                    int precisionDiff = mc.precision - result.precision();
                    int scaleDiff = preferredScale - result.scale();
                    if (precisionDiff >= scaleDiff) return result.setScale(preferredScale); else return result.setScale(result.scale() + precisionDiff);
                }
            }
        }
        long padding = (long)lhs.scale - augend.scale;
        if (padding != 0) {
            BigDecimal[] arg = preAlign(lhs, augend, padding, mc);
            matchScale(arg);
            lhs = arg[0];
            augend = arg[1];
        }
        return new BigDecimal(lhs.inflate().intVal.add(augend.inflate().intVal), lhs.scale).doRound(mc);
    }
    
    private BigDecimal[] preAlign(BigDecimal lhs, BigDecimal augend, long padding, MathContext mc) {
        if (!$assertionsDisabled && !(padding != 0)) throw new AssertionError();
        BigDecimal big;
        BigDecimal small;
        if (padding < 0) {
            big = lhs;
            small = augend;
        } else {
            big = augend;
            small = lhs;
        }
        long estResultUlpScale = (long)big.scale - big.precision() + mc.precision;
        long smallHighDigitPos = (long)small.scale - small.precision() + 1;
        if (smallHighDigitPos > big.scale + 2 && smallHighDigitPos > estResultUlpScale + 2) {
            small = BigDecimal.valueOf(small.signum(), this.checkScale(Math.max(big.scale, estResultUlpScale) + 3));
        }
        BigDecimal[] result = {big, small};
        return result;
    }
    
    public BigDecimal subtract(BigDecimal subtrahend) {
        BigDecimal[] arg = {this, subtrahend};
        matchScale(arg);
        long x = arg[0].intCompact;
        long y = arg[1].intCompact;
        if (x != INFLATED && y != INFLATED) {
            long difference = x - y;
            if (((x ^ y) & (difference ^ x)) >> 63 == 0L) return BigDecimal.valueOf(difference, arg[0].scale);
        }
        return new BigDecimal(arg[0].inflate().intVal.subtract(arg[1].inflate().intVal), arg[0].scale);
    }
    
    public BigDecimal subtract(BigDecimal subtrahend, MathContext mc) {
        if (mc.precision == 0) return subtract(subtrahend);
        this.inflate();
        subtrahend.inflate();
        BigDecimal rhs = new BigDecimal(subtrahend.intVal.negate(), subtrahend.scale);
        rhs.precision = subtrahend.precision;
        return add(rhs, mc);
    }
    
    public BigDecimal multiply(BigDecimal multiplicand) {
        long x = this.intCompact;
        long y = multiplicand.intCompact;
        int productScale = checkScale((long)scale + multiplicand.scale);
        if (x != INFLATED && y != INFLATED) {
            long product = x * y;
            if (!(y != 0L && product / y != x)) return BigDecimal.valueOf(product, productScale);
        }
        BigDecimal result = new BigDecimal(this.inflate().intVal.multiply(multiplicand.inflate().intVal), productScale);
        return result;
    }
    
    public BigDecimal multiply(BigDecimal multiplicand, MathContext mc) {
        if (mc.precision == 0) return multiply(multiplicand);
        BigDecimal lhs = this;
        return lhs.inflate().multiply(multiplicand.inflate()).doRound(mc);
    }
    
    public BigDecimal divide(BigDecimal divisor, int scale, int roundingMode) {
        if (roundingMode < ROUND_UP || roundingMode > ROUND_UNNECESSARY) throw new IllegalArgumentException("Invalid rounding mode");
        BigDecimal dividend;
        if (checkScale((long)scale + divisor.scale) >= this.scale) {
            dividend = this.setScale(scale + divisor.scale);
        } else {
            dividend = this;
            divisor = divisor.setScale(checkScale((long)this.scale - scale));
        }
        boolean compact = dividend.intCompact != INFLATED && divisor.intCompact != INFLATED;
        long div = INFLATED;
        long rem = INFLATED;
        ;
        BigInteger q = null;
        BigInteger r = null;
        if (compact) {
            div = dividend.intCompact / divisor.intCompact;
            rem = dividend.intCompact % divisor.intCompact;
        } else {
            BigInteger[] i = dividend.inflate().intVal.divideAndRemainder(divisor.inflate().intVal);
            q = i[0];
            r = i[1];
        }
        if (compact) {
            if (rem == 0) return new BigDecimal(div, scale);
        } else {
            if (r.signum() == 0) return new BigDecimal(q, scale);
        }
        if (roundingMode == ROUND_UNNECESSARY) throw new ArithmeticException("Rounding necessary");
        int signum = dividend.signum() * divisor.signum();
        boolean increment;
        if (roundingMode == ROUND_UP) {
            increment = true;
        } else if (roundingMode == ROUND_DOWN) {
            increment = false;
        } else if (roundingMode == ROUND_CEILING) {
            increment = (signum > 0);
        } else if (roundingMode == ROUND_FLOOR) {
            increment = (signum < 0);
        } else {
            int cmpFracHalf;
            if (compact) {
                cmpFracHalf = longCompareTo(Math.abs(2 * rem), Math.abs(divisor.intCompact));
            } else {
                cmpFracHalf = r.add(r).abs().compareTo(divisor.intVal.abs());
            }
            if (cmpFracHalf < 0) {
                increment = false;
            } else if (cmpFracHalf > 0) {
                increment = true;
            } else {
                if (roundingMode == ROUND_HALF_UP) increment = true; else if (roundingMode == ROUND_HALF_DOWN) increment = false; else {
                    if (compact) increment = (div & 1L) != 0L; else increment = q.testBit(0);
                }
            }
        }
        if (compact) {
            if (increment) div += signum;
            return new BigDecimal(div, scale);
        } else {
            return (increment ? new BigDecimal(q.add(BigInteger.valueOf(signum)), scale) : new BigDecimal(q, scale));
        }
    }
    
    public BigDecimal divide(BigDecimal divisor, int scale, RoundingMode roundingMode) {
        return divide(divisor, scale, roundingMode.oldMode);
    }
    
    public BigDecimal divide(BigDecimal divisor, int roundingMode) {
        return this.divide(divisor, scale, roundingMode);
    }
    
    public BigDecimal divide(BigDecimal divisor, RoundingMode roundingMode) {
        return this.divide(divisor, scale, roundingMode.oldMode);
    }
    
    public BigDecimal divide(BigDecimal divisor) {
        if (divisor.signum() == 0) {
            if (this.signum() == 0) throw new ArithmeticException("Division undefined");
            throw new ArithmeticException("Division by zero");
        }
        int preferredScale = (int)Math.max(Math.min((long)this.scale() - divisor.scale(), Integer.MAX_VALUE), Integer.MIN_VALUE);
        if (this.signum() == 0) return new BigDecimal(0, preferredScale); else {
            this.inflate();
            divisor.inflate();
            MathContext mc = new MathContext((int)Math.min(this.precision() + (long)Math.ceil(10.0 * divisor.precision() / 3.0), Integer.MAX_VALUE), RoundingMode.UNNECESSARY);
            BigDecimal quotient;
            try {
                quotient = this.divide(divisor, mc);
            } catch (ArithmeticException e) {
                throw new ArithmeticException("Non-terminating decimal expansion; no exact representable decimal result.");
            }
            int quotientScale = quotient.scale();
            if (preferredScale > quotientScale) return quotient.setScale(preferredScale);
            return quotient;
        }
    }
    
    public BigDecimal divide(BigDecimal divisor, MathContext mc) {
        if (mc.precision == 0) return divide(divisor);
        BigDecimal lhs = this.inflate();
        BigDecimal rhs = divisor.inflate();
        BigDecimal result;
        long preferredScale = (long)lhs.scale() - rhs.scale();
        if (rhs.signum() == 0) {
            if (lhs.signum() == 0) throw new ArithmeticException("Division undefined");
            throw new ArithmeticException("Division by zero");
        }
        if (lhs.signum() == 0) return new BigDecimal(BigInteger.ZERO, (int)Math.max(Math.min(preferredScale, Integer.MAX_VALUE), Integer.MIN_VALUE));
        BigDecimal xprime = new BigDecimal(lhs.intVal.abs(), lhs.precision());
        BigDecimal yprime = new BigDecimal(rhs.intVal.abs(), rhs.precision());
        if (mc.roundingMode == RoundingMode.CEILING || mc.roundingMode == RoundingMode.FLOOR) {
            if ((xprime.signum() != lhs.signum()) ^ (yprime.signum() != rhs.signum())) {
                mc = new MathContext(mc.precision, (mc.roundingMode == RoundingMode.CEILING) ? RoundingMode.FLOOR : RoundingMode.CEILING);
            }
        }
        if (xprime.compareTo(yprime) > 0) yprime.scale -= 1;
        result = xprime.divide(yprime, mc.precision, mc.roundingMode.oldMode);
        result.scale = checkScale((long)yprime.scale - xprime.scale - (rhs.scale - lhs.scale) + mc.precision);
        if (lhs.signum() != rhs.signum()) result = result.negate();
        result = result.doRound(mc);
        if (result.multiply(divisor).compareTo(this) == 0) {
            return result.stripZerosToMatchScale(preferredScale);
        } else {
            return result;
        }
    }
    
    public BigDecimal divideToIntegralValue(BigDecimal divisor) {
        int preferredScale = (int)Math.max(Math.min((long)this.scale() - divisor.scale(), Integer.MAX_VALUE), Integer.MIN_VALUE);
        this.inflate();
        divisor.inflate();
        if (this.abs().compareTo(divisor.abs()) < 0) {
            return BigDecimal.valueOf(0, preferredScale);
        }
        if (this.signum() == 0 && divisor.signum() != 0) return this.setScale(preferredScale);
        int maxDigits = (int)Math.min(this.precision() + (long)Math.ceil(10.0 * divisor.precision() / 3.0) + Math.abs((long)this.scale() - divisor.scale()) + 2, Integer.MAX_VALUE);
        BigDecimal quotient = this.divide(divisor, new MathContext(maxDigits, RoundingMode.DOWN));
        if (quotient.scale > 0) {
            quotient = quotient.setScale(0, RoundingMode.DOWN).stripZerosToMatchScale(preferredScale);
        }
        if (quotient.scale < preferredScale) {
            quotient = quotient.setScale(preferredScale);
        }
        return quotient;
    }
    
    public BigDecimal divideToIntegralValue(BigDecimal divisor, MathContext mc) {
        if (mc.precision == 0 || (this.abs().compareTo(divisor.abs()) < 0)) return divideToIntegralValue(divisor);
        int preferredScale = (int)Math.max(Math.min((long)this.scale() - divisor.scale(), Integer.MAX_VALUE), Integer.MIN_VALUE);
        BigDecimal result = this.divide(divisor, new MathContext(mc.precision, RoundingMode.DOWN));
        int resultScale = result.scale();
        if (result.scale() < 0) {
            BigDecimal product = result.multiply(divisor);
            if (this.subtract(product).abs().compareTo(divisor.abs()) >= 0) {
                throw new ArithmeticException("Division impossible");
            }
        } else if (result.scale() > 0) {
            result = result.setScale(0, RoundingMode.DOWN);
        }
        int precisionDiff;
        if ((preferredScale > result.scale()) && (precisionDiff = mc.precision - result.precision()) > 0) {
            return result.setScale(result.scale() + Math.min(precisionDiff, preferredScale - result.scale));
        } else return result.stripZerosToMatchScale(preferredScale);
    }
    
    public BigDecimal remainder(BigDecimal divisor) {
        BigDecimal[] divrem = this.divideAndRemainder(divisor);
        return divrem[1];
    }
    
    public BigDecimal remainder(BigDecimal divisor, MathContext mc) {
        BigDecimal[] divrem = this.divideAndRemainder(divisor, mc);
        return divrem[1];
    }
    
    public BigDecimal[] divideAndRemainder(BigDecimal divisor) {
        BigDecimal[] result = new BigDecimal[2];
        result[0] = this.divideToIntegralValue(divisor);
        result[1] = this.subtract(result[0].multiply(divisor));
        return result;
    }
    
    public BigDecimal[] divideAndRemainder(BigDecimal divisor, MathContext mc) {
        if (mc.precision == 0) return divideAndRemainder(divisor);
        BigDecimal[] result = new BigDecimal[2];
        BigDecimal lhs = this;
        result[0] = lhs.divideToIntegralValue(divisor, mc);
        result[1] = lhs.subtract(result[0].multiply(divisor));
        return result;
    }
    
    public BigDecimal pow(int n) {
        if (n < 0 || n > 999999999) throw new ArithmeticException("Invalid operation");
        int newScale = checkScale((long)scale * n);
        this.inflate();
        return new BigDecimal(intVal.pow(n), newScale);
    }
    
    public BigDecimal pow(int n, MathContext mc) {
        if (mc.precision == 0) return pow(n);
        if (n < -999999999 || n > 999999999) throw new ArithmeticException("Invalid operation");
        if (n == 0) return ONE;
        this.inflate();
        BigDecimal lhs = this;
        MathContext workmc = mc;
        int mag = Math.abs(n);
        if (mc.precision > 0) {
            int elength = intLength(mag);
            if (elength > mc.precision) throw new ArithmeticException("Invalid operation");
            workmc = new MathContext(mc.precision + elength + 1, mc.roundingMode);
        }
        BigDecimal acc = ONE;
        boolean seenbit = false;
        for (int i = 1; ; i++) {
            mag += mag;
            if (mag < 0) {
                seenbit = true;
                acc = acc.multiply(lhs, workmc);
            }
            if (i == 31) break;
            if (seenbit) acc = acc.multiply(acc, workmc);
        }
        if (n < 0) acc = ONE.divide(acc, workmc);
        return acc.doRound(mc);
    }
    
    public BigDecimal abs() {
        return (signum() < 0 ? negate() : this);
    }
    
    public BigDecimal abs(MathContext mc) {
        return (signum() < 0 ? negate(mc) : plus(mc));
    }
    
    public BigDecimal negate() {
        BigDecimal result;
        if (intCompact != INFLATED) result = BigDecimal.valueOf(-intCompact, scale); else {
            result = new BigDecimal(intVal.negate(), scale);
            result.precision = precision;
        }
        return result;
    }
    
    public BigDecimal negate(MathContext mc) {
        return negate().plus(mc);
    }
    
    public BigDecimal plus() {
        return this;
    }
    
    public BigDecimal plus(MathContext mc) {
        if (mc.precision == 0) return this;
        return this.doRound(mc);
    }
    
    public int signum() {
        return (intCompact != INFLATED) ? Long.signum(intCompact) : intVal.signum();
    }
    
    public int scale() {
        return scale;
    }
    
    public int precision() {
        int result = precision;
        if (result == 0) {
            result = digitLength();
            precision = result;
        }
        return result;
    }
    
    public BigInteger unscaledValue() {
        return this.inflate().intVal;
    }
    public static final int ROUND_UP = 0;
    public static final int ROUND_DOWN = 1;
    public static final int ROUND_CEILING = 2;
    public static final int ROUND_FLOOR = 3;
    public static final int ROUND_HALF_UP = 4;
    public static final int ROUND_HALF_DOWN = 5;
    public static final int ROUND_HALF_EVEN = 6;
    public static final int ROUND_UNNECESSARY = 7;
    
    public BigDecimal round(MathContext mc) {
        return plus(mc);
    }
    
    public BigDecimal setScale(int newScale, RoundingMode roundingMode) {
        return setScale(newScale, roundingMode.oldMode);
    }
    
    public BigDecimal setScale(int newScale, int roundingMode) {
        if (roundingMode < ROUND_UP || roundingMode > ROUND_UNNECESSARY) throw new IllegalArgumentException("Invalid rounding mode");
        if (newScale == this.scale) return this;
        if (this.signum() == 0) return BigDecimal.valueOf(0, newScale);
        if (newScale > this.scale) {
            int raise = checkScale((long)newScale - this.scale);
            if (intCompact != INFLATED) {
                long scaledResult = longTenToThe(intCompact, raise);
                if (scaledResult != INFLATED) return BigDecimal.valueOf(scaledResult, newScale);
                this.inflate();
            }
            BigDecimal result = new BigDecimal(intVal.multiply(tenToThe(raise)), newScale);
            if (this.precision > 0) result.precision = this.precision + newScale - this.scale;
            return result;
        }
        return divide(ONE, newScale, roundingMode);
    }
    
    public BigDecimal setScale(int newScale) {
        return setScale(newScale, ROUND_UNNECESSARY);
    }
    
    public BigDecimal movePointLeft(int n) {
        int newScale = checkScale((long)scale + n);
        BigDecimal num;
        if (intCompact != INFLATED) num = BigDecimal.valueOf(intCompact, newScale); else num = new BigDecimal(intVal, newScale);
        return (num.scale < 0 ? num.setScale(0) : num);
    }
    
    public BigDecimal movePointRight(int n) {
        int newScale = checkScale((long)scale - n);
        BigDecimal num;
        if (intCompact != INFLATED) num = BigDecimal.valueOf(intCompact, newScale); else num = new BigDecimal(intVal, newScale);
        return (num.scale < 0 ? num.setScale(0) : num);
    }
    
    public BigDecimal scaleByPowerOfTen(int n) {
        this.inflate();
        BigDecimal num = new BigDecimal(intVal, checkScale((long)scale - n));
        num.precision = precision;
        return num;
    }
    
    public BigDecimal stripTrailingZeros() {
        this.inflate();
        return (new BigDecimal(intVal, scale)).stripZerosToMatchScale(Long.MIN_VALUE);
    }
    
    public int compareTo(BigDecimal val) {
        int sigDiff = signum() - val.signum();
        if (sigDiff != 0) return (sigDiff > 0 ? 1 : -1);
        int aethis = this.precision() - this.scale;
        int aeval = val.precision() - val.scale;
        if (aethis < aeval) return -this.signum(); else if (aethis > aeval) return this.signum();
        BigDecimal[] arg = {this, val};
        matchScale(arg);
        if (arg[0].intCompact != INFLATED && arg[1].intCompact != INFLATED) return longCompareTo(arg[0].intCompact, arg[1].intCompact);
        return arg[0].inflate().intVal.compareTo(arg[1].inflate().intVal);
    }
    
    public boolean equals(Object x) {
        if (!(x instanceof BigDecimal)) return false;
        BigDecimal xDec = (BigDecimal)(BigDecimal)x;
        if (scale != xDec.scale) return false;
        if (this.intCompact != INFLATED && xDec.intCompact != INFLATED) return this.intCompact == xDec.intCompact;
        return this.inflate().intVal.equals(xDec.inflate().intVal);
    }
    
    public BigDecimal min(BigDecimal val) {
        return (compareTo(val) <= 0 ? this : val);
    }
    
    public BigDecimal max(BigDecimal val) {
        return (compareTo(val) >= 0 ? this : val);
    }
    
    public int hashCode() {
        if (intCompact != INFLATED) {
            long val2 = (intCompact < 0) ? -intCompact : intCompact;
            int temp = (int)(((int)(val2 >>> 32)) * 31 + (val2 & 4294967295L));
            return 31 * ((intCompact < 0) ? -temp : temp) + scale;
        } else return 31 * intVal.hashCode() + scale;
    }
    
    public String toString() {
        if (stringCache == null) stringCache = layoutChars(true);
        return stringCache;
    }
    
    public String toEngineeringString() {
        return layoutChars(false);
    }
    
    public String toPlainString() {
        BigDecimal bd = this;
        if (bd.scale < 0) bd = bd.setScale(0);
        bd.inflate();
        if (bd.scale == 0) return bd.intVal.toString();
        return bd.getValueString(bd.signum(), bd.intVal.abs().toString(), bd.scale);
    }
    
    private String getValueString(int signum, String intString, int scale) {
        StringBuilder buf;
        int insertionPoint = intString.length() - scale;
        if (insertionPoint == 0) {
            return (signum < 0 ? "-0." : "0.") + intString;
        } else if (insertionPoint > 0) {
            buf = new StringBuilder(intString);
            buf.insert(insertionPoint, '.');
            if (signum < 0) buf.insert(0, '-');
        } else {
            buf = new StringBuilder(3 - insertionPoint + intString.length());
            buf.append(signum < 0 ? "-0." : "0.");
            for (int i = 0; i < -insertionPoint; i++) buf.append('0');
            buf.append(intString);
        }
        return buf.toString();
    }
    
    public BigInteger toBigInteger() {
        return this.setScale(0, ROUND_DOWN).inflate().intVal;
    }
    
    public BigInteger toBigIntegerExact() {
        return this.setScale(0, ROUND_UNNECESSARY).inflate().intVal;
    }
    
    public long longValue() {
        return (intCompact != INFLATED && scale == 0) ? intCompact : toBigInteger().longValue();
    }
    
    public long longValueExact() {
        if (intCompact != INFLATED && scale == 0) return intCompact;
        if ((precision() - scale) > 19) throw new java.lang.ArithmeticException("Overflow");
        if (this.signum() == 0) return 0;
        if ((this.precision() - this.scale) <= 0) throw new ArithmeticException("Rounding necessary");
        BigDecimal num = this.setScale(0, ROUND_UNNECESSARY).inflate();
        if (num.precision() >= 19) {
            if (LONGMIN == null) {
                LONGMIN = BigInteger.valueOf(Long.MIN_VALUE);
                LONGMAX = BigInteger.valueOf(Long.MAX_VALUE);
            }
            if ((num.intVal.compareTo(LONGMIN) < 0) || (num.intVal.compareTo(LONGMAX) > 0)) throw new java.lang.ArithmeticException("Overflow");
        }
        return num.intVal.longValue();
    }
    private static BigInteger LONGMIN = null;
    private static BigInteger LONGMAX = null;
    
    public int intValue() {
        return (intCompact != INFLATED && scale == 0) ? (int)intCompact : toBigInteger().intValue();
    }
    
    public int intValueExact() {
        long num;
        num = this.longValueExact();
        if ((int)num != num) throw new java.lang.ArithmeticException("Overflow");
        return (int)num;
    }
    
    public short shortValueExact() {
        long num;
        num = this.longValueExact();
        if ((short)num != num) throw new java.lang.ArithmeticException("Overflow");
        return (short)num;
    }
    
    public byte byteValueExact() {
        long num;
        num = this.longValueExact();
        if ((byte)num != num) throw new java.lang.ArithmeticException("Overflow");
        return (byte)num;
    }
    
    public float floatValue() {
        if (scale == 0 && intCompact != INFLATED) return (float)intCompact;
        return Float.parseFloat(this.toString());
    }
    
    public double doubleValue() {
        if (scale == 0 && intCompact != INFLATED) return (double)intCompact;
        return Double.parseDouble(this.toString());
    }
    
    public BigDecimal ulp() {
        return BigDecimal.valueOf(1, this.scale());
    }
    
    private String layoutChars(boolean sci) {
        if (scale == 0) return (intCompact != INFLATED) ? Long.toString(intCompact) : intVal.toString();
        char[] coeff;
        if (intCompact != INFLATED) coeff = Long.toString(Math.abs(intCompact)).toCharArray(); else coeff = intVal.abs().toString().toCharArray();
        StringBuilder buf = new StringBuilder(coeff.length + 14);
        if (signum() < 0) buf.append('-');
        long adjusted = -(long)scale + (coeff.length - 1);
        if ((scale >= 0) && (adjusted >= -6)) {
            int pad = scale - coeff.length;
            if (pad >= 0) {
                buf.append('0');
                buf.append('.');
                for (; pad > 0; pad--) {
                    buf.append('0');
                }
                buf.append(coeff);
            } else {
                buf.append(coeff, 0, -pad);
                buf.append('.');
                buf.append(coeff, -pad, scale);
            }
        } else {
            if (sci) {
                buf.append(coeff[0]);
                if (coeff.length > 1) {
                    buf.append('.');
                    buf.append(coeff, 1, coeff.length - 1);
                }
            } else {
                int sig = (int)(adjusted % 3);
                if (sig < 0) sig += 3;
                adjusted -= sig;
                sig++;
                if (signum() == 0) {
                    switch (sig) {
                    case 1: 
                        buf.append('0');
                        break;
                    
                    case 2: 
                        buf.append("0.00");
                        adjusted += 3;
                        break;
                    
                    case 3: 
                        buf.append("0.0");
                        adjusted += 3;
                        break;
                    
                    default: 
                        throw new AssertionError("Unexpected sig value " + sig);
                    
                    }
                } else if (sig >= coeff.length) {
                    buf.append(coeff, 0, coeff.length);
                    for (int i = sig - coeff.length; i > 0; i--) buf.append('0');
                } else {
                    buf.append(coeff, 0, sig);
                    buf.append('.');
                    buf.append(coeff, sig, coeff.length - sig);
                }
            }
            if (adjusted != 0) {
                buf.append('E');
                if (adjusted > 0) buf.append('+');
                buf.append(adjusted);
            }
        }
        return buf.toString();
    }
    
    private static BigInteger tenToThe(int n) {
        if (n < TENPOWERS.length) return TENPOWERS[n];
        char[] tenpow = new char[n + 1];
        tenpow[0] = '1';
        for (int i = 1; i <= n; i++) tenpow[i] = '0';
        return new BigInteger(tenpow);
    }
    private static BigInteger[] TENPOWERS = {BigInteger.ONE, BigInteger.valueOf(10), BigInteger.valueOf(100), BigInteger.valueOf(1000), BigInteger.valueOf(10000), BigInteger.valueOf(100000), BigInteger.valueOf(1000000), BigInteger.valueOf(10000000), BigInteger.valueOf(100000000), BigInteger.valueOf(1000000000)};
    
    private static long longTenToThe(long val, int n) {
        if (n >= 0 && n < thresholds.length) {
            if (Math.abs(val) <= thresholds[n][0]) {
                return val * thresholds[n][1];
            }
        }
        return INFLATED;
    }
    private static long[][] thresholds = {{Long.MAX_VALUE, 1L}, {Long.MAX_VALUE / 10L, 10L}, {Long.MAX_VALUE / 100L, 100L}, {Long.MAX_VALUE / 1000L, 1000L}, {Long.MAX_VALUE / 10000L, 10000L}, {Long.MAX_VALUE / 100000L, 100000L}, {Long.MAX_VALUE / 1000000L, 1000000L}, {Long.MAX_VALUE / 10000000L, 10000000L}, {Long.MAX_VALUE / 100000000L, 100000000L}, {Long.MAX_VALUE / 1000000000L, 1000000000L}, {Long.MAX_VALUE / 10000000000L, 10000000000L}, {Long.MAX_VALUE / 100000000000L, 100000000000L}, {Long.MAX_VALUE / 1000000000000L, 1000000000000L}, {Long.MAX_VALUE / 100000000000000L, 10000000000000L}};
    
    private static boolean compactLong(long val) {
        return (val != Long.MIN_VALUE);
    }
    
    private BigDecimal inflate() {
        if (intVal == null) intVal = BigInteger.valueOf(intCompact);
        return this;
    }
    
    private static void matchScale(BigDecimal[] val) {
        if (val[0].scale < val[1].scale) val[0] = val[0].setScale(val[1].scale); else if (val[1].scale < val[0].scale) val[1] = val[1].setScale(val[0].scale);
    }
    
    private synchronized void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        if (intVal == null) {
            String message = "BigDecimal: null intVal in stream";
            throw new java.io.StreamCorruptedException(message);
        }
        intCompact = INFLATED;
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        this.inflate();
        s.defaultWriteObject();
    }
    
    private int digitLength() {
        if (intCompact != INFLATED && Math.abs(intCompact) <= Integer.MAX_VALUE) return intLength(Math.abs((int)intCompact));
        if (signum() == 0) return 1;
        this.inflate();
        BigInteger work = intVal;
        int digits = 0;
        for (; work.mag.length > 1; ) {
            work = work.divide(TENPOWERS[9]);
            digits += 9;
            if (work.signum() == 0) return digits;
        }
        digits += intLength(work.mag[0]);
        return digits;
    }
    private static int[] ilogTable = {0, 9, 99, 999, 9999, 99999, 999999, 9999999, 99999999, 999999999, Integer.MAX_VALUE};
    
    private int intLength(int x) {
        int digits;
        if (x < 0) {
            return 10;
        } else {
            if (x <= 9) return 1;
            for (int i = -1; ; i++) {
                if (x <= ilogTable[i + 1]) return i + 1;
            }
        }
    }
    
    private BigDecimal stripZerosToMatchScale(long preferredScale) {
        boolean compact = (intCompact != INFLATED);
        this.inflate();
        BigInteger[] qr;
        while (intVal.abs().compareTo(BigInteger.TEN) >= 0 && scale > preferredScale) {
            if (intVal.testBit(0)) break;
            qr = intVal.divideAndRemainder(BigInteger.TEN);
            if (qr[1].signum() != 0) break;
            intVal = qr[0];
            scale = checkScale((long)scale - 1);
            if (precision > 0) precision--;
        }
        if (compact) intCompact = intVal.longValue();
        return this;
    }
    
    private int checkScale(long val) {
        if ((int)val != val) {
            if ((this.intCompact != INFLATED && this.intCompact != 0) || (this.intVal != null && this.signum() != 0) || (this.intVal == null && this.intCompact == INFLATED)) {
                if (val > Integer.MAX_VALUE) throw new ArithmeticException("Underflow");
                if (val < Integer.MIN_VALUE) throw new ArithmeticException("Overflow");
            } else {
                return (val > Integer.MAX_VALUE) ? Integer.MAX_VALUE : Integer.MIN_VALUE;
            }
        }
        return (int)val;
    }
    
    private BigDecimal roundOp(MathContext mc) {
        BigDecimal rounded = doRound(mc);
        return rounded;
    }
    
    private void roundThis(MathContext mc) {
        BigDecimal rounded = doRound(mc);
        if (rounded == this) return;
        this.intVal = rounded.intVal;
        this.intCompact = rounded.intCompact;
        this.scale = rounded.scale;
        this.precision = rounded.precision;
    }
    
    private BigDecimal doRound(MathContext mc) {
        this.inflate();
        if (precision == 0) {
            if (mc.roundingMax != null && intVal.compareTo(mc.roundingMax) < 0 && intVal.compareTo(mc.roundingMin) > 0) return this;
            precision();
        }
        int drop = precision - mc.precision;
        if (drop <= 0) return this;
        BigDecimal rounded = dropDigits(mc, drop);
        return rounded.doRound(mc);
    }
    
    private BigDecimal dropDigits(MathContext mc, int drop) {
        BigDecimal divisor = new BigDecimal(tenToThe(drop), 0);
        BigDecimal rounded = this.divide(divisor, scale, mc.roundingMode.oldMode);
        rounded.scale = checkScale((long)rounded.scale - drop);
        return rounded;
    }
    
    private static int longCompareTo(long x, long y) {
        return (x < y) ? -1 : (x == y) ? 0 : 1;
    }
    
    private static void print(String name, BigDecimal bd) {
        System.err.format("%s:\tintCompact %d\tintVal %d\tscale %d\tprecision %d%n", new Object[]{name, Long.valueOf(bd.intCompact), bd.intVal, Integer.valueOf(bd.scale), Integer.valueOf(bd.precision)});
    }
    
    private BigDecimal audit() {
        if (precision > 0) {
            if (precision != digitLength()) {
                print("audit", this);
                throw new AssertionError("precision mismatch");
            }
        }
        if (intCompact == INFLATED) {
            if (intVal == null) {
                print("audit", this);
                throw new AssertionError("null intVal");
            }
        } else {
            if (intVal != null) {
                long val = intVal.longValue();
                if (val != intCompact) {
                    print("audit", this);
                    throw new AssertionError("Inconsistent state, intCompact=" + intCompact + "\t intVal=" + val);
                }
            }
        }
        return this;
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((BigDecimal)x0);
    }
}
