package java.math;

import java.util.Random;
import java.io.*;

public class BigInteger extends Number implements Comparable {
    /*synthetic*/ static final boolean $assertionsDisabled = !BigInteger.class.desiredAssertionStatus();
    int signum;
    int[] mag;
    private int bitCount = -1;
    private int bitLength = -1;
    private int lowestSetBit = -2;
    private int firstNonzeroByteNum = -2;
    private int firstNonzeroIntNum = -2;
    private static final long LONG_MASK = 4294967295L;
    
    public BigInteger(byte[] val) {
        
        if (val.length == 0) throw new NumberFormatException("Zero length BigInteger");
        if (val[0] < 0) {
            mag = makePositive(val);
            signum = -1;
        } else {
            mag = stripLeadingZeroBytes(val);
            signum = (mag.length == 0 ? 0 : 1);
        }
    }
    
    private BigInteger(int[] val) {
        
        if (val.length == 0) throw new NumberFormatException("Zero length BigInteger");
        if (val[0] < 0) {
            mag = makePositive(val);
            signum = -1;
        } else {
            mag = trustedStripLeadingZeroInts(val);
            signum = (mag.length == 0 ? 0 : 1);
        }
    }
    
    public BigInteger(int signum, byte[] magnitude) {
        
        this.mag = stripLeadingZeroBytes(magnitude);
        if (signum < -1 || signum > 1) throw (new NumberFormatException("Invalid signum value"));
        if (this.mag.length == 0) {
            this.signum = 0;
        } else {
            if (signum == 0) throw (new NumberFormatException("signum-magnitude mismatch"));
            this.signum = signum;
        }
    }
    
    private BigInteger(int signum, int[] magnitude) {
        
        this.mag = stripLeadingZeroInts(magnitude);
        if (signum < -1 || signum > 1) throw (new NumberFormatException("Invalid signum value"));
        if (this.mag.length == 0) {
            this.signum = 0;
        } else {
            if (signum == 0) throw (new NumberFormatException("signum-magnitude mismatch"));
            this.signum = signum;
        }
    }
    
    public BigInteger(String val, int radix) {
        
        int cursor = 0;
        int numDigits;
        int len = val.length();
        if (radix < Character.MIN_RADIX || radix > Character.MAX_RADIX) throw new NumberFormatException("Radix out of range");
        if (val.length() == 0) throw new NumberFormatException("Zero length BigInteger");
        signum = 1;
        int index = val.lastIndexOf("-");
        if (index != -1) {
            if (index == 0) {
                if (val.length() == 1) throw new NumberFormatException("Zero length BigInteger");
                signum = -1;
                cursor = 1;
            } else {
                throw new NumberFormatException("Illegal embedded minus sign");
            }
        }
        while (cursor < len && Character.digit(val.charAt(cursor), radix) == 0) cursor++;
        if (cursor == len) {
            signum = 0;
            mag = ZERO.mag;
            return;
        } else {
            numDigits = len - cursor;
        }
        int numBits = (int)(((numDigits * bitsPerDigit[radix]) >>> 10) + 1);
        int numWords = (numBits + 31) / 32;
        mag = new int[numWords];
        int firstGroupLen = numDigits % digitsPerInt[radix];
        if (firstGroupLen == 0) firstGroupLen = digitsPerInt[radix];
        String group = val.substring(cursor, cursor += firstGroupLen);
        mag[mag.length - 1] = Integer.parseInt(group, radix);
        if (mag[mag.length - 1] < 0) throw new NumberFormatException("Illegal digit");
        int superRadix = intRadix[radix];
        int groupVal = 0;
        while (cursor < val.length()) {
            group = val.substring(cursor, cursor += digitsPerInt[radix]);
            groupVal = Integer.parseInt(group, radix);
            if (groupVal < 0) throw new NumberFormatException("Illegal digit");
            destructiveMulAdd(mag, superRadix, groupVal);
        }
        mag = trustedStripLeadingZeroInts(mag);
    }
    
    BigInteger(char[] val) {
        
        int cursor = 0;
        int numDigits;
        int len = val.length;
        signum = 1;
        if (val[0] == '-') {
            if (len == 1) throw new NumberFormatException("Zero length BigInteger");
            signum = -1;
            cursor = 1;
        }
        while (cursor < len && Character.digit(val[cursor], 10) == 0) cursor++;
        if (cursor == len) {
            signum = 0;
            mag = ZERO.mag;
            return;
        } else {
            numDigits = len - cursor;
        }
        int numWords;
        if (len < 10) {
            numWords = 1;
        } else {
            int numBits = (int)(((numDigits * bitsPerDigit[10]) >>> 10) + 1);
            numWords = (numBits + 31) / 32;
        }
        mag = new int[numWords];
        int firstGroupLen = numDigits % digitsPerInt[10];
        if (firstGroupLen == 0) firstGroupLen = digitsPerInt[10];
        mag[mag.length - 1] = parseInt(val, cursor, cursor += firstGroupLen);
        while (cursor < len) {
            int groupVal = parseInt(val, cursor, cursor += digitsPerInt[10]);
            destructiveMulAdd(mag, intRadix[10], groupVal);
        }
        mag = trustedStripLeadingZeroInts(mag);
    }
    
    private int parseInt(char[] source, int start, int end) {
        int result = Character.digit(source[start++], 10);
        if (result == -1) throw new NumberFormatException(new String(source));
        for (int index = start; index < end; index++) {
            int nextVal = Character.digit(source[index], 10);
            if (nextVal == -1) throw new NumberFormatException(new String(source));
            result = 10 * result + nextVal;
        }
        return result;
    }
    private static long[] bitsPerDigit = {0, 0, 1024, 1624, 2048, 2378, 2648, 2875, 3072, 3247, 3402, 3543, 3672, 3790, 3899, 4001, 4096, 4186, 4271, 4350, 4426, 4498, 4567, 4633, 4696, 4756, 4814, 4870, 4923, 4975, 5025, 5074, 5120, 5166, 5210, 5253, 5295};
    
    private static void destructiveMulAdd(int[] x, int y, int z) {
        long ylong = y & LONG_MASK;
        long zlong = z & LONG_MASK;
        int len = x.length;
        long product = 0;
        long carry = 0;
        for (int i = len - 1; i >= 0; i--) {
            product = ylong * (x[i] & LONG_MASK) + carry;
            x[i] = (int)product;
            carry = product >>> 32;
        }
        long sum = (x[len - 1] & LONG_MASK) + zlong;
        x[len - 1] = (int)sum;
        carry = sum >>> 32;
        for (int i = len - 2; i >= 0; i--) {
            sum = (x[i] & LONG_MASK) + carry;
            x[i] = (int)sum;
            carry = sum >>> 32;
        }
    }
    
    public BigInteger(String val) {
        this(val, 10);
    }
    
    public BigInteger(int numBits, Random rnd) {
        this(1, randomBits(numBits, rnd));
    }
    
    private static byte[] randomBits(int numBits, Random rnd) {
        if (numBits < 0) throw new IllegalArgumentException("numBits must be non-negative");
        int numBytes = (numBits + 7) / 8;
        byte[] randomBits = new byte[numBytes];
        if (numBytes > 0) {
            rnd.nextBytes(randomBits);
            int excessBits = 8 * numBytes - numBits;
            randomBits[0] &= (1 << (8 - excessBits)) - 1;
        }
        return randomBits;
    }
    
    public BigInteger(int bitLength, int certainty, Random rnd) {
        
        BigInteger prime;
        if (bitLength < 2) throw new ArithmeticException("bitLength < 2");
        prime = (bitLength < 95 ? smallPrime(bitLength, certainty, rnd) : largePrime(bitLength, certainty, rnd));
        signum = 1;
        mag = prime.mag;
    }
    private static final int SMALL_PRIME_THRESHOLD = 95;
    private static final int DEFAULT_PRIME_CERTAINTY = 100;
    
    public static BigInteger probablePrime(int bitLength, Random rnd) {
        if (bitLength < 2) throw new ArithmeticException("bitLength < 2");
        return (bitLength < SMALL_PRIME_THRESHOLD ? smallPrime(bitLength, DEFAULT_PRIME_CERTAINTY, rnd) : largePrime(bitLength, DEFAULT_PRIME_CERTAINTY, rnd));
    }
    
    private static BigInteger smallPrime(int bitLength, int certainty, Random rnd) {
        int magLen = (bitLength + 31) >>> 5;
        int[] temp = new int[magLen];
        int highBit = 1 << ((bitLength + 31) & 31);
        int highMask = (highBit << 1) - 1;
        while (true) {
            for (int i = 0; i < magLen; i++) temp[i] = rnd.nextInt();
            temp[0] = (temp[0] & highMask) | highBit;
            if (bitLength > 2) temp[magLen - 1] |= 1;
            BigInteger p = new BigInteger(temp, 1);
            if (bitLength > 6) {
                long r = p.remainder(SMALL_PRIME_PRODUCT).longValue();
                if ((r % 3 == 0) || (r % 5 == 0) || (r % 7 == 0) || (r % 11 == 0) || (r % 13 == 0) || (r % 17 == 0) || (r % 19 == 0) || (r % 23 == 0) || (r % 29 == 0) || (r % 31 == 0) || (r % 37 == 0) || (r % 41 == 0)) continue;
            }
            if (bitLength < 4) return p;
            if (p.primeToCertainty(certainty)) return p;
        }
    }
    private static final BigInteger SMALL_PRIME_PRODUCT = valueOf(3L * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 37 * 41);
    
    private static BigInteger largePrime(int bitLength, int certainty, Random rnd) {
        BigInteger p;
        p = new BigInteger(bitLength, rnd).setBit(bitLength - 1);
        p.mag[p.mag.length - 1] &= -2;
        int searchLen = (bitLength / 20) * 64;
        BitSieve searchSieve = new BitSieve(p, searchLen);
        BigInteger candidate = searchSieve.retrieve(p, certainty);
        while ((candidate == null) || (candidate.bitLength() != bitLength)) {
            p = p.add(BigInteger.valueOf(2 * searchLen));
            if (p.bitLength() != bitLength) p = new BigInteger(bitLength, rnd).setBit(bitLength - 1);
            p.mag[p.mag.length - 1] &= -2;
            searchSieve = new BitSieve(p, searchLen);
            candidate = searchSieve.retrieve(p, certainty);
        }
        return candidate;
    }
    
    public BigInteger nextProbablePrime() {
        if (this.signum < 0) throw new ArithmeticException("start < 0: " + this);
        if ((this.signum == 0) || this.equals(ONE)) return TWO;
        BigInteger result = this.add(ONE);
        if (result.bitLength() < SMALL_PRIME_THRESHOLD) {
            if (!result.testBit(0)) result = result.add(ONE);
            while (true) {
                if (result.bitLength() > 6) {
                    long r = result.remainder(SMALL_PRIME_PRODUCT).longValue();
                    if ((r % 3 == 0) || (r % 5 == 0) || (r % 7 == 0) || (r % 11 == 0) || (r % 13 == 0) || (r % 17 == 0) || (r % 19 == 0) || (r % 23 == 0) || (r % 29 == 0) || (r % 31 == 0) || (r % 37 == 0) || (r % 41 == 0)) {
                        result = result.add(TWO);
                        continue;
                    }
                }
                if (result.bitLength() < 4) return result;
                if (result.primeToCertainty(DEFAULT_PRIME_CERTAINTY)) return result;
                result = result.add(TWO);
            }
        }
        if (result.testBit(0)) result = result.subtract(ONE);
        int searchLen = (result.bitLength() / 20) * 64;
        while (true) {
            BitSieve searchSieve = new BitSieve(result, searchLen);
            BigInteger candidate = searchSieve.retrieve(result, DEFAULT_PRIME_CERTAINTY);
            if (candidate != null) return candidate;
            result = result.add(BigInteger.valueOf(2 * searchLen));
        }
    }
    
    boolean primeToCertainty(int certainty) {
        int rounds = 0;
        int n = (Math.min(certainty, Integer.MAX_VALUE - 1) + 1) / 2;
        int sizeInBits = this.bitLength();
        if (sizeInBits < 100) {
            rounds = 50;
            rounds = n < rounds ? n : rounds;
            return passesMillerRabin(rounds);
        }
        if (sizeInBits < 256) {
            rounds = 27;
        } else if (sizeInBits < 512) {
            rounds = 15;
        } else if (sizeInBits < 768) {
            rounds = 8;
        } else if (sizeInBits < 1024) {
            rounds = 4;
        } else {
            rounds = 2;
        }
        rounds = n < rounds ? n : rounds;
        return passesMillerRabin(rounds) && passesLucasLehmer();
    }
    
    private boolean passesLucasLehmer() {
        BigInteger thisPlusOne = this.add(ONE);
        int d = 5;
        while (jacobiSymbol(d, this) != -1) {
            d = (d < 0) ? Math.abs(d) + 2 : -(d + 2);
        }
        BigInteger u = lucasLehmerSequence(d, thisPlusOne, this);
        return u.mod(this).equals(ZERO);
    }
    
    private static int jacobiSymbol(int p, BigInteger n) {
        if (p == 0) return 0;
        int j = 1;
        int u = n.mag[n.mag.length - 1];
        if (p < 0) {
            p = -p;
            int n8 = u & 7;
            if ((n8 == 3) || (n8 == 7)) j = -j;
        }
        while ((p & 3) == 0) p >>= 2;
        if ((p & 1) == 0) {
            p >>= 1;
            if (((u ^ (u >> 1)) & 2) != 0) j = -j;
        }
        if (p == 1) return j;
        if ((p & u & 2) != 0) j = -j;
        u = n.mod(BigInteger.valueOf(p)).intValue();
        while (u != 0) {
            while ((u & 3) == 0) u >>= 2;
            if ((u & 1) == 0) {
                u >>= 1;
                if (((p ^ (p >> 1)) & 2) != 0) j = -j;
            }
            if (u == 1) return j;
            if (!$assertionsDisabled && !(u < p)) throw new AssertionError();
            int t = u;
            u = p;
            p = t;
            if ((u & p & 2) != 0) j = -j;
            u %= p;
        }
        return 0;
    }
    
    private static BigInteger lucasLehmerSequence(int z, BigInteger k, BigInteger n) {
        BigInteger d = BigInteger.valueOf(z);
        BigInteger u = ONE;
        BigInteger u2;
        BigInteger v = ONE;
        BigInteger v2;
        for (int i = k.bitLength() - 2; i >= 0; i--) {
            u2 = u.multiply(v).mod(n);
            v2 = v.square().add(d.multiply(u.square())).mod(n);
            if (v2.testBit(0)) {
                v2 = n.subtract(v2);
                v2.signum = -v2.signum;
            }
            v2 = v2.shiftRight(1);
            u = u2;
            v = v2;
            if (k.testBit(i)) {
                u2 = u.add(v).mod(n);
                if (u2.testBit(0)) {
                    u2 = n.subtract(u2);
                    u2.signum = -u2.signum;
                }
                u2 = u2.shiftRight(1);
                v2 = v.add(d.multiply(u)).mod(n);
                if (v2.testBit(0)) {
                    v2 = n.subtract(v2);
                    v2.signum = -v2.signum;
                }
                v2 = v2.shiftRight(1);
                u = u2;
                v = v2;
            }
        }
        return u;
    }
    
    private boolean passesMillerRabin(int iterations) {
        BigInteger thisMinusOne = this.subtract(ONE);
        BigInteger m = thisMinusOne;
        int a = m.getLowestSetBit();
        m = m.shiftRight(a);
        Random rnd = new Random();
        for (int i = 0; i < iterations; i++) {
            BigInteger b;
            do {
                b = new BigInteger(this.bitLength(), rnd);
            }             while (b.compareTo(ONE) <= 0 || b.compareTo(this) >= 0);
            int j = 0;
            BigInteger z = b.modPow(m, this);
            while (!((j == 0 && z.equals(ONE)) || z.equals(thisMinusOne))) {
                if (j > 0 && z.equals(ONE) || ++j == a) return false;
                z = z.modPow(TWO, this);
            }
        }
        return true;
    }
    
    private BigInteger(int[] magnitude, int signum) {
        
        this.signum = (magnitude.length == 0 ? 0 : signum);
        this.mag = magnitude;
    }
    
    private BigInteger(byte[] magnitude, int signum) {
        
        this.signum = (magnitude.length == 0 ? 0 : signum);
        this.mag = stripLeadingZeroBytes(magnitude);
    }
    
    BigInteger(MutableBigInteger val, int sign) {
        
        if (val.offset > 0 || val.value.length != val.intLen) {
            mag = new int[val.intLen];
            for (int i = 0; i < val.intLen; i++) mag[i] = val.value[val.offset + i];
        } else {
            mag = val.value;
        }
        this.signum = (val.intLen == 0) ? 0 : sign;
    }
    
    public static BigInteger valueOf(long val) {
        if (val == 0) return ZERO;
        if (val > 0 && val <= MAX_CONSTANT) return posConst[(int)val]; else if (val < 0 && val >= -MAX_CONSTANT) return negConst[(int)-val];
        return new BigInteger(val);
    }
    
    private BigInteger(long val) {
        
        if (val < 0) {
            signum = -1;
            val = -val;
        } else {
            signum = 1;
        }
        int highWord = (int)(val >>> 32);
        if (highWord == 0) {
            mag = new int[1];
            mag[0] = (int)val;
        } else {
            mag = new int[2];
            mag[0] = highWord;
            mag[1] = (int)val;
        }
    }
    
    private static BigInteger valueOf(int[] val) {
        return (val[0] > 0 ? new BigInteger(val, 1) : new BigInteger(val));
    }
    private static final int MAX_CONSTANT = 16;
    private static BigInteger[] posConst = new BigInteger[MAX_CONSTANT + 1];
    private static BigInteger[] negConst = new BigInteger[MAX_CONSTANT + 1];
    static {
        for (int i = 1; i <= MAX_CONSTANT; i++) {
            int[] magnitude = new int[1];
            magnitude[0] = (int)i;
            posConst[i] = new BigInteger(magnitude, 1);
            negConst[i] = new BigInteger(magnitude, -1);
        }
    }
    public static final BigInteger ZERO = new BigInteger(new int[0], 0);
    public static final BigInteger ONE = valueOf(1);
    private static final BigInteger TWO = valueOf(2);
    public static final BigInteger TEN = valueOf(10);
    
    public BigInteger add(BigInteger val) {
        int[] resultMag;
        if (val.signum == 0) return this;
        if (signum == 0) return val;
        if (val.signum == signum) return new BigInteger(add(mag, val.mag), signum);
        int cmp = intArrayCmp(mag, val.mag);
        if (cmp == 0) return ZERO;
        resultMag = (cmp > 0 ? subtract(mag, val.mag) : subtract(val.mag, mag));
        resultMag = trustedStripLeadingZeroInts(resultMag);
        return new BigInteger(resultMag, cmp * signum);
    }
    
    private static int[] add(int[] x, int[] y) {
        if (x.length < y.length) {
            int[] tmp = x;
            x = y;
            y = tmp;
        }
        int xIndex = x.length;
        int yIndex = y.length;
        int[] result = new int[xIndex];
        long sum = 0;
        while (yIndex > 0) {
            sum = (x[--xIndex] & LONG_MASK) + (y[--yIndex] & LONG_MASK) + (sum >>> 32);
            result[xIndex] = (int)sum;
        }
        boolean carry = (sum >>> 32 != 0);
        while (xIndex > 0 && carry) carry = ((result[--xIndex] = x[xIndex] + 1) == 0);
        while (xIndex > 0) result[--xIndex] = x[xIndex];
        if (carry) {
            int newLen = result.length + 1;
            int[] temp = new int[newLen];
            for (int i = 1; i < newLen; i++) temp[i] = result[i - 1];
            temp[0] = 1;
            result = temp;
        }
        return result;
    }
    
    public BigInteger subtract(BigInteger val) {
        int[] resultMag;
        if (val.signum == 0) return this;
        if (signum == 0) return val.negate();
        if (val.signum != signum) return new BigInteger(add(mag, val.mag), signum);
        int cmp = intArrayCmp(mag, val.mag);
        if (cmp == 0) return ZERO;
        resultMag = (cmp > 0 ? subtract(mag, val.mag) : subtract(val.mag, mag));
        resultMag = trustedStripLeadingZeroInts(resultMag);
        return new BigInteger(resultMag, cmp * signum);
    }
    
    private static int[] subtract(int[] big, int[] little) {
        int bigIndex = big.length;
        int[] result = new int[bigIndex];
        int littleIndex = little.length;
        long difference = 0;
        while (littleIndex > 0) {
            difference = (big[--bigIndex] & LONG_MASK) - (little[--littleIndex] & LONG_MASK) + (difference >> 32);
            result[bigIndex] = (int)difference;
        }
        boolean borrow = (difference >> 32 != 0);
        while (bigIndex > 0 && borrow) borrow = ((result[--bigIndex] = big[bigIndex] - 1) == -1);
        while (bigIndex > 0) result[--bigIndex] = big[bigIndex];
        return result;
    }
    
    public BigInteger multiply(BigInteger val) {
        if (signum == 0 || val.signum == 0) return ZERO;
        int[] result = multiplyToLen(mag, mag.length, val.mag, val.mag.length, null);
        result = trustedStripLeadingZeroInts(result);
        return new BigInteger(result, signum * val.signum);
    }
    
    private int[] multiplyToLen(int[] x, int xlen, int[] y, int ylen, int[] z) {
        int xstart = xlen - 1;
        int ystart = ylen - 1;
        if (z == null || z.length < (xlen + ylen)) z = new int[xlen + ylen];
        long carry = 0;
        for (int j = ystart, k = ystart + 1 + xstart; j >= 0; j--, k--) {
            long product = (y[j] & LONG_MASK) * (x[xstart] & LONG_MASK) + carry;
            z[k] = (int)product;
            carry = product >>> 32;
        }
        z[xstart] = (int)carry;
        for (int i = xstart - 1; i >= 0; i--) {
            carry = 0;
            for (int j = ystart, k = ystart + 1 + i; j >= 0; j--, k--) {
                long product = (y[j] & LONG_MASK) * (x[i] & LONG_MASK) + (z[k] & LONG_MASK) + carry;
                z[k] = (int)product;
                carry = product >>> 32;
            }
            z[i] = (int)carry;
        }
        return z;
    }
    
    private BigInteger square() {
        if (signum == 0) return ZERO;
        int[] z = squareToLen(mag, mag.length, null);
        return new BigInteger(trustedStripLeadingZeroInts(z), 1);
    }
    
    private static final int[] squareToLen(int[] x, int len, int[] z) {
        int zlen = len << 1;
        if (z == null || z.length < zlen) z = new int[zlen];
        int lastProductLowWord = 0;
        for (int j = 0, i = 0; j < len; j++) {
            long piece = (x[j] & LONG_MASK);
            long product = piece * piece;
            z[i++] = (lastProductLowWord << 31) | (int)(product >>> 33);
            z[i++] = (int)(product >>> 1);
            lastProductLowWord = (int)product;
        }
        for (int i = len, offset = 1; i > 0; i--, offset += 2) {
            int t = x[i - 1];
            t = mulAdd(z, x, offset, i - 1, t);
            addOne(z, offset - 1, i, t);
        }
        primitiveLeftShift(z, zlen, 1);
        z[zlen - 1] |= x[len - 1] & 1;
        return z;
    }
    
    public BigInteger divide(BigInteger val) {
        MutableBigInteger q = new MutableBigInteger();
        MutableBigInteger r = new MutableBigInteger();
        MutableBigInteger a = new MutableBigInteger(this.mag);
        MutableBigInteger b = new MutableBigInteger(val.mag);
        a.divide(b, q, r);
        return new BigInteger(q, this.signum * val.signum);
    }
    
    public BigInteger[] divideAndRemainder(BigInteger val) {
        BigInteger[] result = new BigInteger[2];
        MutableBigInteger q = new MutableBigInteger();
        MutableBigInteger r = new MutableBigInteger();
        MutableBigInteger a = new MutableBigInteger(this.mag);
        MutableBigInteger b = new MutableBigInteger(val.mag);
        a.divide(b, q, r);
        result[0] = new BigInteger(q, this.signum * val.signum);
        result[1] = new BigInteger(r, this.signum);
        return result;
    }
    
    public BigInteger remainder(BigInteger val) {
        MutableBigInteger q = new MutableBigInteger();
        MutableBigInteger r = new MutableBigInteger();
        MutableBigInteger a = new MutableBigInteger(this.mag);
        MutableBigInteger b = new MutableBigInteger(val.mag);
        a.divide(b, q, r);
        return new BigInteger(r, this.signum);
    }
    
    public BigInteger pow(int exponent) {
        if (exponent < 0) throw new ArithmeticException("Negative exponent");
        if (signum == 0) return (exponent == 0 ? ONE : this);
        int newSign = (signum < 0 && (exponent & 1) == 1 ? -1 : 1);
        int[] baseToPow2 = this.mag;
        int[] result = {1};
        while (exponent != 0) {
            if ((exponent & 1) == 1) {
                result = multiplyToLen(result, result.length, baseToPow2, baseToPow2.length, null);
                result = trustedStripLeadingZeroInts(result);
            }
            if ((exponent >>>= 1) != 0) {
                baseToPow2 = squareToLen(baseToPow2, baseToPow2.length, null);
                baseToPow2 = trustedStripLeadingZeroInts(baseToPow2);
            }
        }
        return new BigInteger(result, newSign);
    }
    
    public BigInteger gcd(BigInteger val) {
        if (val.signum == 0) return this.abs(); else if (this.signum == 0) return val.abs();
        MutableBigInteger a = new MutableBigInteger(this);
        MutableBigInteger b = new MutableBigInteger(val);
        MutableBigInteger result = a.hybridGCD(b);
        return new BigInteger(result, 1);
    }
    
    private static int[] leftShift(int[] a, int len, int n) {
        int nInts = n >>> 5;
        int nBits = n & 31;
        int bitsInHighWord = bitLen(a[0]);
        if (n <= (32 - bitsInHighWord)) {
            primitiveLeftShift(a, len, nBits);
            return a;
        } else {
            if (nBits <= (32 - bitsInHighWord)) {
                int[] result = new int[nInts + len];
                for (int i = 0; i < len; i++) result[i] = a[i];
                primitiveLeftShift(result, result.length, nBits);
                return result;
            } else {
                int[] result = new int[nInts + len + 1];
                for (int i = 0; i < len; i++) result[i] = a[i];
                primitiveRightShift(result, result.length, 32 - nBits);
                return result;
            }
        }
    }
    
    static void primitiveRightShift(int[] a, int len, int n) {
        int n2 = 32 - n;
        for (int i = len - 1, c = a[i]; i > 0; i--) {
            int b = c;
            c = a[i - 1];
            a[i] = (c << n2) | (b >>> n);
        }
        a[0] >>>= n;
    }
    
    static void primitiveLeftShift(int[] a, int len, int n) {
        if (len == 0 || n == 0) return;
        int n2 = 32 - n;
        for (int i = 0, c = a[i], m = i + len - 1; i < m; i++) {
            int b = c;
            c = a[i + 1];
            a[i] = (b << n) | (c >>> n2);
        }
        a[len - 1] <<= n;
    }
    
    private static int bitLength(int[] val, int len) {
        if (len == 0) return 0;
        return ((len - 1) << 5) + bitLen(val[0]);
    }
    
    public BigInteger abs() {
        return (signum >= 0 ? this : this.negate());
    }
    
    public BigInteger negate() {
        return new BigInteger(this.mag, -this.signum);
    }
    
    public int signum() {
        return this.signum;
    }
    
    public BigInteger mod(BigInteger m) {
        if (m.signum <= 0) throw new ArithmeticException("BigInteger: modulus not positive");
        BigInteger result = this.remainder(m);
        return (result.signum >= 0 ? result : result.add(m));
    }
    
    public BigInteger modPow(BigInteger exponent, BigInteger m) {
        if (m.signum <= 0) throw new ArithmeticException("BigInteger: modulus not positive");
        if (exponent.signum == 0) return (m.equals(ONE) ? ZERO : ONE);
        if (this.equals(ONE)) return (m.equals(ONE) ? ZERO : ONE);
        if (this.equals(ZERO) && exponent.signum >= 0) return ZERO;
        if (this.equals(negConst[1]) && (!exponent.testBit(0))) return (m.equals(ONE) ? ZERO : ONE);
        boolean invertResult;
        if (invertResult = (exponent.signum < 0)) exponent = exponent.negate();
        BigInteger base = (this.signum < 0 || this.compareTo(m) >= 0 ? this.mod(m) : this);
        BigInteger result;
        if (m.testBit(0)) {
            result = base.oddModPow(exponent, m);
        } else {
            int p = m.getLowestSetBit();
            BigInteger m1 = m.shiftRight(p);
            BigInteger m2 = ONE.shiftLeft(p);
            BigInteger base2 = (this.signum < 0 || this.compareTo(m1) >= 0 ? this.mod(m1) : this);
            BigInteger a1 = (m1.equals(ONE) ? ZERO : base2.oddModPow(exponent, m1));
            BigInteger a2 = base.modPow2(exponent, p);
            BigInteger y1 = m2.modInverse(m1);
            BigInteger y2 = m1.modInverse(m2);
            result = a1.multiply(m2).multiply(y1).add(a2.multiply(m1).multiply(y2)).mod(m);
        }
        return (invertResult ? result.modInverse(m) : result);
    }
    static int[] bnExpModThreshTable = {7, 25, 81, 241, 673, 1793, Integer.MAX_VALUE};
    
    private BigInteger oddModPow(BigInteger y, BigInteger z) {
        if (y.equals(ONE)) return this;
        if (signum == 0) return ZERO;
        int[] base = (int[])(int[])mag.clone();
        int[] exp = y.mag;
        int[] mod = z.mag;
        int modLen = mod.length;
        int wbits = 0;
        int ebits = bitLength(exp, exp.length);
        if ((ebits != 17) || (exp[0] != 65537)) {
            while (ebits > bnExpModThreshTable[wbits]) {
                wbits++;
            }
        }
        int tblmask = 1 << wbits;
        int[][] table = new int[tblmask][];
        for (int i = 0; i < tblmask; i++) table[i] = new int[modLen];
        int inv = -MutableBigInteger.inverseMod32(mod[modLen - 1]);
        int[] a = leftShift(base, base.length, modLen << 5);
        MutableBigInteger q = new MutableBigInteger();
        MutableBigInteger r = new MutableBigInteger();
        MutableBigInteger a2 = new MutableBigInteger(a);
        MutableBigInteger b2 = new MutableBigInteger(mod);
        a2.divide(b2, q, r);
        table[0] = r.toIntArray();
        if (table[0].length < modLen) {
            int offset = modLen - table[0].length;
            int[] t2 = new int[modLen];
            for (int i = 0; i < table[0].length; i++) t2[i + offset] = table[0][i];
            table[0] = t2;
        }
        int[] b = squareToLen(table[0], modLen, null);
        b = montReduce(b, mod, modLen, inv);
        int[] t = new int[modLen];
        for (int i = 0; i < modLen; i++) t[i] = b[i];
        for (int i = 1; i < tblmask; i++) {
            int[] prod = multiplyToLen(t, modLen, table[i - 1], modLen, null);
            table[i] = montReduce(prod, mod, modLen, inv);
        }
        int bitpos = 1 << ((ebits - 1) & (32 - 1));
        int buf = 0;
        int elen = exp.length;
        int eIndex = 0;
        for (int i = 0; i <= wbits; i++) {
            buf = (buf << 1) | (((exp[eIndex] & bitpos) != 0) ? 1 : 0);
            bitpos >>>= 1;
            if (bitpos == 0) {
                eIndex++;
                bitpos = 1 << (32 - 1);
                elen--;
            }
        }
        int multpos = ebits;
        ebits--;
        boolean isone = true;
        multpos = ebits - wbits;
        while ((buf & 1) == 0) {
            buf >>>= 1;
            multpos++;
        }
        int[] mult = table[buf >>> 1];
        buf = 0;
        if (multpos == ebits) isone = false;
        while (true) {
            ebits--;
            buf <<= 1;
            if (elen != 0) {
                buf |= ((exp[eIndex] & bitpos) != 0) ? 1 : 0;
                bitpos >>>= 1;
                if (bitpos == 0) {
                    eIndex++;
                    bitpos = 1 << (32 - 1);
                    elen--;
                }
            }
            if ((buf & tblmask) != 0) {
                multpos = ebits - wbits;
                while ((buf & 1) == 0) {
                    buf >>>= 1;
                    multpos++;
                }
                mult = table[buf >>> 1];
                buf = 0;
            }
            if (ebits == multpos) {
                if (isone) {
                    b = (int[])(int[])mult.clone();
                    isone = false;
                } else {
                    t = b;
                    a = multiplyToLen(t, modLen, mult, modLen, a);
                    a = montReduce(a, mod, modLen, inv);
                    t = a;
                    a = b;
                    b = t;
                }
            }
            if (ebits == 0) break;
            if (!isone) {
                t = b;
                a = squareToLen(t, modLen, a);
                a = montReduce(a, mod, modLen, inv);
                t = a;
                a = b;
                b = t;
            }
        }
        int[] t2 = new int[2 * modLen];
        for (int i = 0; i < modLen; i++) t2[i + modLen] = b[i];
        b = montReduce(t2, mod, modLen, inv);
        t2 = new int[modLen];
        for (int i = 0; i < modLen; i++) t2[i] = b[i];
        return new BigInteger(1, t2);
    }
    
    private static int[] montReduce(int[] n, int[] mod, int mlen, int inv) {
        int c = 0;
        int len = mlen;
        int offset = 0;
        do {
            int nEnd = n[n.length - 1 - offset];
            int carry = mulAdd(n, mod, offset, mlen, inv * nEnd);
            c += addOne(n, offset, mlen, carry);
            offset++;
        }         while (--len > 0);
        while (c > 0) c += subN(n, mod, mlen);
        while (intArrayCmpToLen(n, mod, mlen) >= 0) subN(n, mod, mlen);
        return n;
    }
    
    private static int intArrayCmpToLen(int[] arg1, int[] arg2, int len) {
        for (int i = 0; i < len; i++) {
            long b1 = arg1[i] & LONG_MASK;
            long b2 = arg2[i] & LONG_MASK;
            if (b1 < b2) return -1;
            if (b1 > b2) return 1;
        }
        return 0;
    }
    
    private static int subN(int[] a, int[] b, int len) {
        long sum = 0;
        while (--len >= 0) {
            sum = (a[len] & LONG_MASK) - (b[len] & LONG_MASK) + (sum >> 32);
            a[len] = (int)sum;
        }
        return (int)(sum >> 32);
    }
    
    static int mulAdd(int[] out, int[] in, int offset, int len, int k) {
        long kLong = k & LONG_MASK;
        long carry = 0;
        offset = out.length - offset - 1;
        for (int j = len - 1; j >= 0; j--) {
            long product = (in[j] & LONG_MASK) * kLong + (out[offset] & LONG_MASK) + carry;
            out[offset--] = (int)product;
            carry = product >>> 32;
        }
        return (int)carry;
    }
    
    static int addOne(int[] a, int offset, int mlen, int carry) {
        offset = a.length - 1 - mlen - offset;
        long t = (a[offset] & LONG_MASK) + (carry & LONG_MASK);
        a[offset] = (int)t;
        if ((t >>> 32) == 0) return 0;
        while (--mlen >= 0) {
            if (--offset < 0) {
                return 1;
            } else {
                a[offset]++;
                if (a[offset] != 0) return 0;
            }
        }
        return 1;
    }
    
    private BigInteger modPow2(BigInteger exponent, int p) {
        BigInteger result = valueOf(1);
        BigInteger baseToPow2 = this.mod2(p);
        int expOffset = 0;
        int limit = exponent.bitLength();
        if (this.testBit(0)) limit = (p - 1) < limit ? (p - 1) : limit;
        while (expOffset < limit) {
            if (exponent.testBit(expOffset)) result = result.multiply(baseToPow2).mod2(p);
            expOffset++;
            if (expOffset < limit) baseToPow2 = baseToPow2.square().mod2(p);
        }
        return result;
    }
    
    private BigInteger mod2(int p) {
        if (bitLength() <= p) return this;
        int numInts = (p + 31) / 32;
        int[] mag = new int[numInts];
        for (int i = 0; i < numInts; i++) mag[i] = this.mag[i + (this.mag.length - numInts)];
        int excessBits = (numInts << 5) - p;
        mag[0] &= (1L << (32 - excessBits)) - 1;
        return (mag[0] == 0 ? new BigInteger(1, mag) : new BigInteger(mag, 1));
    }
    
    public BigInteger modInverse(BigInteger m) {
        if (m.signum != 1) throw new ArithmeticException("BigInteger: modulus not positive");
        if (m.equals(ONE)) return ZERO;
        BigInteger modVal = this;
        if (signum < 0 || (intArrayCmp(mag, m.mag) >= 0)) modVal = this.mod(m);
        if (modVal.equals(ONE)) return ONE;
        MutableBigInteger a = new MutableBigInteger(modVal);
        MutableBigInteger b = new MutableBigInteger(m);
        MutableBigInteger result = a.mutableModInverse(b);
        return new BigInteger(result, 1);
    }
    
    public BigInteger shiftLeft(int n) {
        if (signum == 0) return ZERO;
        if (n == 0) return this;
        if (n < 0) return shiftRight(-n);
        int nInts = n >>> 5;
        int nBits = n & 31;
        int magLen = mag.length;
        int[] newMag = null;
        if (nBits == 0) {
            newMag = new int[magLen + nInts];
            for (int i = 0; i < magLen; i++) newMag[i] = mag[i];
        } else {
            int i = 0;
            int nBits2 = 32 - nBits;
            int highBits = mag[0] >>> nBits2;
            if (highBits != 0) {
                newMag = new int[magLen + nInts + 1];
                newMag[i++] = highBits;
            } else {
                newMag = new int[magLen + nInts];
            }
            int j = 0;
            while (j < magLen - 1) newMag[i++] = mag[j++] << nBits | mag[j] >>> nBits2;
            newMag[i] = mag[j] << nBits;
        }
        return new BigInteger(newMag, signum);
    }
    
    public BigInteger shiftRight(int n) {
        if (n == 0) return this;
        if (n < 0) return shiftLeft(-n);
        int nInts = n >>> 5;
        int nBits = n & 31;
        int magLen = mag.length;
        int[] newMag = null;
        if (nInts >= magLen) return (signum >= 0 ? ZERO : negConst[1]);
        if (nBits == 0) {
            int newMagLen = magLen - nInts;
            newMag = new int[newMagLen];
            for (int i = 0; i < newMagLen; i++) newMag[i] = mag[i];
        } else {
            int i = 0;
            int highBits = mag[0] >>> nBits;
            if (highBits != 0) {
                newMag = new int[magLen - nInts];
                newMag[i++] = highBits;
            } else {
                newMag = new int[magLen - nInts - 1];
            }
            int nBits2 = 32 - nBits;
            int j = 0;
            while (j < magLen - nInts - 1) newMag[i++] = (mag[j++] << nBits2) | (mag[j] >>> nBits);
        }
        if (signum < 0) {
            boolean onesLost = false;
            for (int i = magLen - 1, j = magLen - nInts; i >= j && !onesLost; i--) onesLost = (mag[i] != 0);
            if (!onesLost && nBits != 0) onesLost = (mag[magLen - nInts - 1] << (32 - nBits) != 0);
            if (onesLost) newMag = javaIncrement(newMag);
        }
        return new BigInteger(newMag, signum);
    }
    
    int[] javaIncrement(int[] val) {
        boolean done = false;
        int lastSum = 0;
        for (int i = val.length - 1; i >= 0 && lastSum == 0; i--) lastSum = (val[i] += 1);
        if (lastSum == 0) {
            val = new int[val.length + 1];
            val[0] = 1;
        }
        return val;
    }
    
    public BigInteger and(BigInteger val) {
        int[] result = new int[Math.max(intLength(), val.intLength())];
        for (int i = 0; i < result.length; i++) result[i] = (int)(getInt(result.length - i - 1) & val.getInt(result.length - i - 1));
        return valueOf(result);
    }
    
    public BigInteger or(BigInteger val) {
        int[] result = new int[Math.max(intLength(), val.intLength())];
        for (int i = 0; i < result.length; i++) result[i] = (int)(getInt(result.length - i - 1) | val.getInt(result.length - i - 1));
        return valueOf(result);
    }
    
    public BigInteger xor(BigInteger val) {
        int[] result = new int[Math.max(intLength(), val.intLength())];
        for (int i = 0; i < result.length; i++) result[i] = (int)(getInt(result.length - i - 1) ^ val.getInt(result.length - i - 1));
        return valueOf(result);
    }
    
    public BigInteger not() {
        int[] result = new int[intLength()];
        for (int i = 0; i < result.length; i++) result[i] = (int)~getInt(result.length - i - 1);
        return valueOf(result);
    }
    
    public BigInteger andNot(BigInteger val) {
        int[] result = new int[Math.max(intLength(), val.intLength())];
        for (int i = 0; i < result.length; i++) result[i] = (int)(getInt(result.length - i - 1) & ~val.getInt(result.length - i - 1));
        return valueOf(result);
    }
    
    public boolean testBit(int n) {
        if (n < 0) throw new ArithmeticException("Negative bit address");
        return (getInt(n / 32) & (1 << (n % 32))) != 0;
    }
    
    public BigInteger setBit(int n) {
        if (n < 0) throw new ArithmeticException("Negative bit address");
        int intNum = n / 32;
        int[] result = new int[Math.max(intLength(), intNum + 2)];
        for (int i = 0; i < result.length; i++) result[result.length - i - 1] = getInt(i);
        result[result.length - intNum - 1] |= (1 << (n % 32));
        return valueOf(result);
    }
    
    public BigInteger clearBit(int n) {
        if (n < 0) throw new ArithmeticException("Negative bit address");
        int intNum = n / 32;
        int[] result = new int[Math.max(intLength(), (n + 1) / 32 + 1)];
        for (int i = 0; i < result.length; i++) result[result.length - i - 1] = getInt(i);
        result[result.length - intNum - 1] &= ~(1 << (n % 32));
        return valueOf(result);
    }
    
    public BigInteger flipBit(int n) {
        if (n < 0) throw new ArithmeticException("Negative bit address");
        int intNum = n / 32;
        int[] result = new int[Math.max(intLength(), intNum + 2)];
        for (int i = 0; i < result.length; i++) result[result.length - i - 1] = getInt(i);
        result[result.length - intNum - 1] ^= (1 << (n % 32));
        return valueOf(result);
    }
    
    public int getLowestSetBit() {
        if (lowestSetBit == -2) {
            if (signum == 0) {
                lowestSetBit = -1;
            } else {
                int i;
                int b;
                for (i = 0; (b = getInt(i)) == 0; i++) ;
                lowestSetBit = (i << 5) + trailingZeroCnt(b);
            }
        }
        return lowestSetBit;
    }
    
    public int bitLength() {
        if (bitLength == -1) {
            if (signum == 0) {
                bitLength = 0;
            } else {
                int magBitLength = ((mag.length - 1) << 5) + bitLen(mag[0]);
                if (signum < 0) {
                    boolean pow2 = (bitCnt(mag[0]) == 1);
                    for (int i = 1; i < mag.length && pow2; i++) pow2 = (mag[i] == 0);
                    bitLength = (pow2 ? magBitLength - 1 : magBitLength);
                } else {
                    bitLength = magBitLength;
                }
            }
        }
        return bitLength;
    }
    
    static int bitLen(int w) {
        return (w < 1 << 15 ? (w < 1 << 7 ? (w < 1 << 3 ? (w < 1 << 1 ? (w < 1 << 0 ? (w < 0 ? 32 : 0) : 1) : (w < 1 << 2 ? 2 : 3)) : (w < 1 << 5 ? (w < 1 << 4 ? 4 : 5) : (w < 1 << 6 ? 6 : 7))) : (w < 1 << 11 ? (w < 1 << 9 ? (w < 1 << 8 ? 8 : 9) : (w < 1 << 10 ? 10 : 11)) : (w < 1 << 13 ? (w < 1 << 12 ? 12 : 13) : (w < 1 << 14 ? 14 : 15)))) : (w < 1 << 23 ? (w < 1 << 19 ? (w < 1 << 17 ? (w < 1 << 16 ? 16 : 17) : (w < 1 << 18 ? 18 : 19)) : (w < 1 << 21 ? (w < 1 << 20 ? 20 : 21) : (w < 1 << 22 ? 22 : 23))) : (w < 1 << 27 ? (w < 1 << 25 ? (w < 1 << 24 ? 24 : 25) : (w < 1 << 26 ? 26 : 27)) : (w < 1 << 29 ? (w < 1 << 28 ? 28 : 29) : (w < 1 << 30 ? 30 : 31)))));
    }
    static final byte[] trailingZeroTable = {-25, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 6, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 7, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 6, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0};
    
    public int bitCount() {
        if (bitCount == -1) {
            int magBitCount = 0;
            for (int i = 0; i < mag.length; i++) magBitCount += bitCnt(mag[i]);
            if (signum < 0) {
                int magTrailingZeroCount = 0;
                int j;
                for (j = mag.length - 1; mag[j] == 0; j--) magTrailingZeroCount += 32;
                magTrailingZeroCount += trailingZeroCnt(mag[j]);
                bitCount = magBitCount + magTrailingZeroCount - 1;
            } else {
                bitCount = magBitCount;
            }
        }
        return bitCount;
    }
    
    static int bitCnt(int val) {
        val -= (-1431655766 & val) >>> 1;
        val = (val & 858993459) + ((val >>> 2) & 858993459);
        val = val + (val >>> 4) & 252645135;
        val += val >>> 8;
        val += val >>> 16;
        return val & 255;
    }
    
    static int trailingZeroCnt(int val) {
        int byteVal = val & 255;
        if (byteVal != 0) return trailingZeroTable[byteVal];
        byteVal = (val >>> 8) & 255;
        if (byteVal != 0) return trailingZeroTable[byteVal] + 8;
        byteVal = (val >>> 16) & 255;
        if (byteVal != 0) return trailingZeroTable[byteVal] + 16;
        byteVal = (val >>> 24) & 255;
        return trailingZeroTable[byteVal] + 24;
    }
    
    public boolean isProbablePrime(int certainty) {
        if (certainty <= 0) return true;
        BigInteger w = this.abs();
        if (w.equals(TWO)) return true;
        if (!w.testBit(0) || w.equals(ONE)) return false;
        return w.primeToCertainty(certainty);
    }
    
    public int compareTo(BigInteger val) {
        return (signum == val.signum ? signum * intArrayCmp(mag, val.mag) : (signum > val.signum ? 1 : -1));
    }
    
    private static int intArrayCmp(int[] arg1, int[] arg2) {
        if (arg1.length < arg2.length) return -1;
        if (arg1.length > arg2.length) return 1;
        for (int i = 0; i < arg1.length; i++) {
            long b1 = arg1[i] & LONG_MASK;
            long b2 = arg2[i] & LONG_MASK;
            if (b1 < b2) return -1;
            if (b1 > b2) return 1;
        }
        return 0;
    }
    
    public boolean equals(Object x) {
        if (x == this) return true;
        if (!(x instanceof BigInteger)) return false;
        BigInteger xInt = (BigInteger)(BigInteger)x;
        if (xInt.signum != signum || xInt.mag.length != mag.length) return false;
        for (int i = 0; i < mag.length; i++) if (xInt.mag[i] != mag[i]) return false;
        return true;
    }
    
    public BigInteger min(BigInteger val) {
        return (compareTo(val) < 0 ? this : val);
    }
    
    public BigInteger max(BigInteger val) {
        return (compareTo(val) > 0 ? this : val);
    }
    
    public int hashCode() {
        int hashCode = 0;
        for (int i = 0; i < mag.length; i++) hashCode = (int)(31 * hashCode + (mag[i] & LONG_MASK));
        return hashCode * signum;
    }
    
    public String toString(int radix) {
        if (signum == 0) return "0";
        if (radix < Character.MIN_RADIX || radix > Character.MAX_RADIX) radix = 10;
        int maxNumDigitGroups = (4 * mag.length + 6) / 7;
        String[] digitGroup = new String[maxNumDigitGroups];
        BigInteger tmp = this.abs();
        int numGroups = 0;
        while (tmp.signum != 0) {
            BigInteger d = longRadix[radix];
            MutableBigInteger q = new MutableBigInteger();
            MutableBigInteger r = new MutableBigInteger();
            MutableBigInteger a = new MutableBigInteger(tmp.mag);
            MutableBigInteger b = new MutableBigInteger(d.mag);
            a.divide(b, q, r);
            BigInteger q2 = new BigInteger(q, tmp.signum * d.signum);
            BigInteger r2 = new BigInteger(r, tmp.signum * d.signum);
            digitGroup[numGroups++] = Long.toString(r2.longValue(), radix);
            tmp = q2;
        }
        StringBuilder buf = new StringBuilder(numGroups * digitsPerLong[radix] + 1);
        if (signum < 0) buf.append('-');
        buf.append(digitGroup[numGroups - 1]);
        for (int i = numGroups - 2; i >= 0; i--) {
            int numLeadingZeros = digitsPerLong[radix] - digitGroup[i].length();
            if (numLeadingZeros != 0) buf.append(zeros[numLeadingZeros]);
            buf.append(digitGroup[i]);
        }
        return buf.toString();
    }
    private static String[] zeros = new String[64];
    static {
        zeros[63] = "000000000000000000000000000000000000000000000000000000000000000";
        for (int i = 0; i < 63; i++) zeros[i] = zeros[63].substring(0, i);
    }
    
    public String toString() {
        return toString(10);
    }
    
    public byte[] toByteArray() {
        int byteLen = bitLength() / 8 + 1;
        byte[] byteArray = new byte[byteLen];
        for (int i = byteLen - 1, bytesCopied = 4, nextInt = 0, intIndex = 0; i >= 0; i--) {
            if (bytesCopied == 4) {
                nextInt = getInt(intIndex++);
                bytesCopied = 1;
            } else {
                nextInt >>>= 8;
                bytesCopied++;
            }
            byteArray[i] = (byte)nextInt;
        }
        return byteArray;
    }
    
    public int intValue() {
        int result = 0;
        result = getInt(0);
        return result;
    }
    
    public long longValue() {
        long result = 0;
        for (int i = 1; i >= 0; i--) result = (result << 32) + (getInt(i) & LONG_MASK);
        return result;
    }
    
    public float floatValue() {
        return Float.parseFloat(this.toString());
    }
    
    public double doubleValue() {
        return Double.parseDouble(this.toString());
    }
    
    private static int[] stripLeadingZeroInts(int[] val) {
        int byteLength = val.length;
        int keep;
        for (keep = 0; keep < val.length && val[keep] == 0; keep++) ;
        int[] result = new int[val.length - keep];
        for (int i = 0; i < val.length - keep; i++) result[i] = val[keep + i];
        return result;
    }
    
    private static int[] trustedStripLeadingZeroInts(int[] val) {
        int byteLength = val.length;
        int keep;
        for (keep = 0; keep < val.length && val[keep] == 0; keep++) ;
        if (keep > 0) {
            int[] result = new int[val.length - keep];
            for (int i = 0; i < val.length - keep; i++) result[i] = val[keep + i];
            return result;
        }
        return val;
    }
    
    private static int[] stripLeadingZeroBytes(byte[] a) {
        int byteLength = a.length;
        int keep;
        for (keep = 0; keep < a.length && a[keep] == 0; keep++) ;
        int intLength = ((byteLength - keep) + 3) / 4;
        int[] result = new int[intLength];
        int b = byteLength - 1;
        for (int i = intLength - 1; i >= 0; i--) {
            result[i] = a[b--] & 255;
            int bytesRemaining = b - keep + 1;
            int bytesToTransfer = Math.min(3, bytesRemaining);
            for (int j = 8; j <= 8 * bytesToTransfer; j += 8) result[i] |= ((a[b--] & 255) << j);
        }
        return result;
    }
    
    private static int[] makePositive(byte[] a) {
        int keep;
        int k;
        int byteLength = a.length;
        for (keep = 0; keep < byteLength && a[keep] == -1; keep++) ;
        for (k = keep; k < byteLength && a[k] == 0; k++) ;
        int extraByte = (k == byteLength) ? 1 : 0;
        int intLength = ((byteLength - keep + extraByte) + 3) / 4;
        int[] result = new int[intLength];
        int b = byteLength - 1;
        for (int i = intLength - 1; i >= 0; i--) {
            result[i] = a[b--] & 255;
            int numBytesToTransfer = Math.min(3, b - keep + 1);
            if (numBytesToTransfer < 0) numBytesToTransfer = 0;
            for (int j = 8; j <= 8 * numBytesToTransfer; j += 8) result[i] |= ((a[b--] & 255) << j);
            int mask = -1 >>> (8 * (3 - numBytesToTransfer));
            result[i] = ~result[i] & mask;
        }
        for (int i = result.length - 1; i >= 0; i--) {
            result[i] = (int)((result[i] & LONG_MASK) + 1);
            if (result[i] != 0) break;
        }
        return result;
    }
    
    private static int[] makePositive(int[] a) {
        int keep;
        int j;
        for (keep = 0; keep < a.length && a[keep] == -1; keep++) ;
        for (j = keep; j < a.length && a[j] == 0; j++) ;
        int extraInt = (j == a.length ? 1 : 0);
        int[] result = new int[a.length - keep + extraInt];
        for (int i = keep; i < a.length; i++) result[i - keep + extraInt] = ~a[i];
        for (int i = result.length - 1; ++result[i] == 0; i--) ;
        return result;
    }
    private static int[] digitsPerLong = {0, 0, 62, 39, 31, 27, 24, 22, 20, 19, 18, 18, 17, 17, 16, 16, 15, 15, 15, 14, 14, 14, 14, 13, 13, 13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12};
    private static BigInteger[] longRadix = {null, null, valueOf(4611686018427387904L), valueOf(4052555153018976267L), valueOf(4611686018427387904L), valueOf(7450580596923828125L), valueOf(4738381338321616896L), valueOf(3909821048582988049L), valueOf(1152921504606846976L), valueOf(1350851717672992089L), valueOf(1000000000000000000L), valueOf(5559917313492231481L), valueOf(2218611106740436992L), valueOf(8650415919381337933L), valueOf(2177953337809371136L), valueOf(6568408355712890625L), valueOf(1152921504606846976L), valueOf(2862423051509815793L), valueOf(6746640616477458432L), valueOf(799006685782884121L), valueOf(1638400000000000000L), valueOf(3243919932521508681L), valueOf(6221821273427820544L), valueOf(504036361936467383L), valueOf(876488338465357824L), valueOf(1490116119384765625L), valueOf(2481152873203736576L), valueOf(4052555153018976267L), valueOf(6502111422497947648L), valueOf(353814783205469041L), valueOf(531441000000000000L), valueOf(787662783788549761L), valueOf(1152921504606846976L), valueOf(1667889514952984961L), valueOf(2386420683693101056L), valueOf(3379220508056640625L), valueOf(4738381338321616896L)};
    private static int[] digitsPerInt = {0, 0, 30, 19, 15, 13, 11, 11, 10, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5};
    private static int[] intRadix = {0, 0, 1073741824, 1162261467, 1073741824, 1220703125, 362797056, 1977326743, 1073741824, 387420489, 1000000000, 214358881, 429981696, 815730721, 1475789056, 170859375, 268435456, 410338673, 612220032, 893871739, 1280000000, 1801088541, 113379904, 148035889, 191102976, 244140625, 308915776, 387420489, 481890304, 594823321, 729000000, 887503681, 1073741824, 1291467969, 1544804416, 1838265625, 60466176};
    
    private int intLength() {
        return bitLength() / 32 + 1;
    }
    
    private int signBit() {
        return (signum < 0 ? 1 : 0);
    }
    
    private int signInt() {
        return (int)(signum < 0 ? -1 : 0);
    }
    
    private int getInt(int n) {
        if (n < 0) return 0;
        if (n >= mag.length) return signInt();
        int magInt = mag[mag.length - n - 1];
        return (int)(signum >= 0 ? magInt : (n <= firstNonzeroIntNum() ? -magInt : ~magInt));
    }
    
    private int firstNonzeroIntNum() {
        if (firstNonzeroIntNum == -2) {
            int i;
            for (i = mag.length - 1; i >= 0 && mag[i] == 0; i--) ;
            firstNonzeroIntNum = mag.length - i - 1;
        }
        return firstNonzeroIntNum;
    }
    private static final long serialVersionUID = -8287574255936472291L;
    private static final ObjectStreamField[] serialPersistentFields = {new ObjectStreamField("signum", Integer.TYPE), new ObjectStreamField("magnitude", byte[].class), new ObjectStreamField("bitCount", Integer.TYPE), new ObjectStreamField("bitLength", Integer.TYPE), new ObjectStreamField("firstNonzeroByteNum", Integer.TYPE), new ObjectStreamField("lowestSetBit", Integer.TYPE)};
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        ObjectInputStream$GetField fields = s.readFields();
        signum = (int)fields.get("signum", -2);
        byte[] magnitude = (byte[])(byte[])fields.get("magnitude", null);
        if (signum < -1 || signum > 1) {
            String message = "BigInteger: Invalid signum value";
            if (fields.defaulted("signum")) message = "BigInteger: Signum not present in stream";
            throw new java.io.StreamCorruptedException(message);
        }
        if ((magnitude.length == 0) != (signum == 0)) {
            String message = "BigInteger: signum-magnitude mismatch";
            if (fields.defaulted("magnitude")) message = "BigInteger: Magnitude not present in stream";
            throw new java.io.StreamCorruptedException(message);
        }
        bitCount = bitLength = -1;
        lowestSetBit = firstNonzeroByteNum = firstNonzeroIntNum = -2;
        mag = stripLeadingZeroBytes(magnitude);
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        ObjectOutputStream$PutField fields = s.putFields();
        fields.put("signum", signum);
        fields.put("magnitude", magSerializedForm());
        fields.put("bitCount", -1);
        fields.put("bitLength", -1);
        fields.put("lowestSetBit", -2);
        fields.put("firstNonzeroByteNum", -2);
        s.writeFields();
    }
    
    private byte[] magSerializedForm() {
        int bitLen = (mag.length == 0 ? 0 : ((mag.length - 1) << 5) + bitLen(mag[0]));
        int byteLen = (bitLen + 7) / 8;
        byte[] result = new byte[byteLen];
        for (int i = byteLen - 1, bytesCopied = 4, intIndex = mag.length - 1, nextInt = 0; i >= 0; i--) {
            if (bytesCopied == 4) {
                nextInt = mag[intIndex--];
                bytesCopied = 1;
            } else {
                nextInt >>>= 8;
                bytesCopied++;
            }
            result[i] = (byte)nextInt;
        }
        return result;
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((BigInteger)x0);
    }
}
