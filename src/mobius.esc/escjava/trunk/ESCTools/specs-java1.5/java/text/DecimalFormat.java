package java.text;

import java.io.InvalidObjectException;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Currency;
import java.util.Hashtable;
import java.util.Locale;
import java.util.ResourceBundle;
import sun.text.resources.LocaleData;

public class DecimalFormat extends NumberFormat {
    /*synthetic*/ static final boolean $assertionsDisabled = !DecimalFormat.class.desiredAssertionStatus();
    
    public DecimalFormat() {
        
        Locale def = Locale.getDefault();
        String pattern = (String)(String)cachedLocaleData.get(def);
        if (pattern == null) {
            ResourceBundle rb = LocaleData.getLocaleElements(def);
            String[] all = rb.getStringArray("NumberPatterns");
            pattern = all[0];
            cachedLocaleData.put(def, pattern);
        }
        this.symbols = new DecimalFormatSymbols(def);
        applyPattern(pattern, false);
    }
    
    public DecimalFormat(String pattern) {
        
        this.symbols = new DecimalFormatSymbols(Locale.getDefault());
        applyPattern(pattern, false);
    }
    
    public DecimalFormat(String pattern, DecimalFormatSymbols symbols) {
        
        this.symbols = (DecimalFormatSymbols)(DecimalFormatSymbols)symbols.clone();
        applyPattern(pattern, false);
    }
    
    public final StringBuffer format(Object number, StringBuffer toAppendTo, FieldPosition pos) {
        if (number instanceof Long || number instanceof Integer || number instanceof Short || number instanceof Byte || (number instanceof BigInteger && ((BigInteger)(BigInteger)number).bitLength() < 64)) {
            return format(((Number)(Number)number).longValue(), toAppendTo, pos);
        } else if (number instanceof BigDecimal) {
            return format((BigDecimal)(BigDecimal)number, toAppendTo, pos);
        } else if (number instanceof BigInteger) {
            return format((BigInteger)(BigInteger)number, toAppendTo, pos);
        } else if (number instanceof Number) {
            return format(((Number)(Number)number).doubleValue(), toAppendTo, pos);
        } else {
            throw new IllegalArgumentException("Cannot format given Object as a Number");
        }
    }
    
    public StringBuffer format(double number, StringBuffer result, FieldPosition fieldPosition) {
        fieldPosition.setBeginIndex(0);
        fieldPosition.setEndIndex(0);
        return format(number, result, fieldPosition.getFieldDelegate());
    }
    
    private StringBuffer format(double number, StringBuffer result, Format$FieldDelegate delegate) {
        if (Double.isNaN(number) || (Double.isInfinite(number) && multiplier == 0)) {
            int iFieldStart = result.length();
            result.append(symbols.getNaN());
            delegate.formatted(INTEGER_FIELD, NumberFormat$Field.INTEGER, NumberFormat$Field.INTEGER, iFieldStart, result.length(), result);
            return result;
        }
        boolean isNegative = ((number < 0.0) || (number == 0.0 && 1 / number < 0.0)) ^ (multiplier < 0);
        if (multiplier != 1) {
            number *= multiplier;
        }
        if (Double.isInfinite(number)) {
            if (isNegative) {
                append(result, negativePrefix, delegate, getNegativePrefixFieldPositions(), NumberFormat$Field.SIGN);
            } else {
                append(result, positivePrefix, delegate, getPositivePrefixFieldPositions(), NumberFormat$Field.SIGN);
            }
            int iFieldStart = result.length();
            result.append(symbols.getInfinity());
            delegate.formatted(INTEGER_FIELD, NumberFormat$Field.INTEGER, NumberFormat$Field.INTEGER, iFieldStart, result.length(), result);
            if (isNegative) {
                append(result, negativeSuffix, delegate, getNegativeSuffixFieldPositions(), NumberFormat$Field.SIGN);
            } else {
                append(result, positiveSuffix, delegate, getPositiveSuffixFieldPositions(), NumberFormat$Field.SIGN);
            }
            return result;
        }
        if (isNegative) {
            number = -number;
        }
        if (!$assertionsDisabled && !(number >= 0 && !Double.isInfinite(number))) throw new AssertionError();
        synchronized (digitList) {
            int maxIntDigits = super.getMaximumIntegerDigits();
            int minIntDigits = super.getMinimumIntegerDigits();
            int maxFraDigits = super.getMaximumFractionDigits();
            int minFraDigits = super.getMinimumFractionDigits();
            digitList.set(number, useExponentialNotation ? maxIntDigits + maxFraDigits : maxFraDigits, !useExponentialNotation);
            return subformat(result, delegate, isNegative, false, maxIntDigits, minIntDigits, maxFraDigits, minFraDigits);
        }
    }
    
    public StringBuffer format(long number, StringBuffer result, FieldPosition fieldPosition) {
        fieldPosition.setBeginIndex(0);
        fieldPosition.setEndIndex(0);
        return format(number, result, fieldPosition.getFieldDelegate());
    }
    
    private StringBuffer format(long number, StringBuffer result, Format$FieldDelegate delegate) {
        boolean isNegative = (number < 0);
        if (isNegative) {
            number = -number;
        }
        boolean useBigInteger = false;
        if (number < 0) {
            if (multiplier != 0) {
                useBigInteger = true;
            }
        } else if (multiplier != 1 && multiplier != 0) {
            long cutoff = Long.MAX_VALUE / multiplier;
            if (cutoff < 0) {
                cutoff = -cutoff;
            }
            useBigInteger = (number > cutoff);
        }
        if (useBigInteger) {
            if (isNegative) {
                number = -number;
            }
            BigInteger bigIntegerValue = BigInteger.valueOf(number);
            return format(bigIntegerValue, result, delegate, true);
        }
        number *= multiplier;
        if (number == 0) {
            isNegative = false;
        } else {
            if (multiplier < 0) {
                number = -number;
                isNegative = !isNegative;
            }
        }
        synchronized (digitList) {
            int maxIntDigits = super.getMaximumIntegerDigits();
            int minIntDigits = super.getMinimumIntegerDigits();
            int maxFraDigits = super.getMaximumFractionDigits();
            int minFraDigits = super.getMinimumFractionDigits();
            digitList.set(number, useExponentialNotation ? maxIntDigits + maxFraDigits : 0);
            return subformat(result, delegate, isNegative, true, maxIntDigits, minIntDigits, maxFraDigits, minFraDigits);
        }
    }
    
    private StringBuffer format(BigDecimal number, StringBuffer result, FieldPosition fieldPosition) {
        fieldPosition.setBeginIndex(0);
        fieldPosition.setEndIndex(0);
        return format(number, result, fieldPosition.getFieldDelegate());
    }
    
    private StringBuffer format(BigDecimal number, StringBuffer result, Format$FieldDelegate delegate) {
        if (multiplier != 1) {
            number = number.multiply(getBigDecimalMultiplier());
        }
        boolean isNegative = number.signum() == -1;
        if (isNegative) {
            number = number.negate();
        }
        synchronized (digitList) {
            int maxIntDigits = getMaximumIntegerDigits();
            int minIntDigits = getMinimumIntegerDigits();
            int maxFraDigits = getMaximumFractionDigits();
            int minFraDigits = getMinimumFractionDigits();
            int maximumDigits = maxIntDigits + maxFraDigits;
            digitList.set(number, useExponentialNotation ? ((maximumDigits < 0) ? Integer.MAX_VALUE : maximumDigits) : maxFraDigits, !useExponentialNotation);
            return subformat(result, delegate, isNegative, false, maxIntDigits, minIntDigits, maxFraDigits, minFraDigits);
        }
    }
    
    private StringBuffer format(BigInteger number, StringBuffer result, FieldPosition fieldPosition) {
        fieldPosition.setBeginIndex(0);
        fieldPosition.setEndIndex(0);
        return format(number, result, fieldPosition.getFieldDelegate(), false);
    }
    
    private StringBuffer format(BigInteger number, StringBuffer result, Format$FieldDelegate delegate, boolean formatLong) {
        if (multiplier != 1) {
            number = number.multiply(getBigIntegerMultiplier());
        }
        boolean isNegative = number.signum() == -1;
        if (isNegative) {
            number = number.negate();
        }
        synchronized (digitList) {
            int maxIntDigits;
            int minIntDigits;
            int maxFraDigits;
            int minFraDigits;
            int maximumDigits;
            if (formatLong) {
                maxIntDigits = super.getMaximumIntegerDigits();
                minIntDigits = super.getMinimumIntegerDigits();
                maxFraDigits = super.getMaximumFractionDigits();
                minFraDigits = super.getMinimumFractionDigits();
                maximumDigits = maxIntDigits + maxFraDigits;
            } else {
                maxIntDigits = getMaximumIntegerDigits();
                minIntDigits = getMinimumIntegerDigits();
                maxFraDigits = getMaximumFractionDigits();
                minFraDigits = getMinimumFractionDigits();
                maximumDigits = maxIntDigits + maxFraDigits;
                if (maximumDigits < 0) {
                    maximumDigits = Integer.MAX_VALUE;
                }
            }
            digitList.set(number, useExponentialNotation ? maximumDigits : 0);
            return subformat(result, delegate, isNegative, true, maxIntDigits, minIntDigits, maxFraDigits, minFraDigits);
        }
    }
    
    public AttributedCharacterIterator formatToCharacterIterator(Object obj) {
        CharacterIteratorFieldDelegate delegate = new CharacterIteratorFieldDelegate();
        StringBuffer sb = new StringBuffer();
        if (obj instanceof Double || obj instanceof Float) {
            format(((Number)(Number)obj).doubleValue(), sb, delegate);
        } else if (obj instanceof Long || obj instanceof Integer || obj instanceof Short || obj instanceof Byte) {
            format(((Number)(Number)obj).longValue(), sb, delegate);
        } else if (obj instanceof BigDecimal) {
            format((BigDecimal)(BigDecimal)obj, sb, delegate);
        } else if (obj instanceof BigInteger) {
            format((BigInteger)(BigInteger)obj, sb, delegate, false);
        } else if (obj == null) {
            throw new NullPointerException("formatToCharacterIterator must be passed non-null object");
        } else {
            throw new IllegalArgumentException("Cannot format given Object as a Number");
        }
        return delegate.getIterator(sb.toString());
    }
    
    private StringBuffer subformat(StringBuffer result, Format$FieldDelegate delegate, boolean isNegative, boolean isInteger, int maxIntDigits, int minIntDigits, int maxFraDigits, int minFraDigits) {
        char zero = symbols.getZeroDigit();
        int zeroDelta = zero - '0';
        char grouping = symbols.getGroupingSeparator();
        char decimal = isCurrencyFormat ? symbols.getMonetaryDecimalSeparator() : symbols.getDecimalSeparator();
        if (digitList.isZero()) {
            digitList.decimalAt = 0;
        }
        if (isNegative) {
            append(result, negativePrefix, delegate, getNegativePrefixFieldPositions(), NumberFormat$Field.SIGN);
        } else {
            append(result, positivePrefix, delegate, getPositivePrefixFieldPositions(), NumberFormat$Field.SIGN);
        }
        if (useExponentialNotation) {
            int iFieldStart = result.length();
            int iFieldEnd = -1;
            int fFieldStart = -1;
            int exponent = digitList.decimalAt;
            int repeat = maxIntDigits;
            int minimumIntegerDigits = minIntDigits;
            if (repeat > 1 && repeat > minIntDigits) {
                if (exponent >= 1) {
                    exponent = ((exponent - 1) / repeat) * repeat;
                } else {
                    exponent = ((exponent - repeat) / repeat) * repeat;
                }
                minimumIntegerDigits = 1;
            } else {
                exponent -= minimumIntegerDigits;
            }
            int minimumDigits = minIntDigits + minFraDigits;
            if (minimumDigits < 0) {
                minimumDigits = Integer.MAX_VALUE;
            }
            int integerDigits = digitList.isZero() ? minimumIntegerDigits : digitList.decimalAt - exponent;
            if (minimumDigits < integerDigits) {
                minimumDigits = integerDigits;
            }
            int totalDigits = digitList.count;
            if (minimumDigits > totalDigits) {
                totalDigits = minimumDigits;
            }
            boolean addedDecimalSeparator = false;
            for (int i = 0; i < totalDigits; ++i) {
                if (i == integerDigits) {
                    iFieldEnd = result.length();
                    result.append(decimal);
                    addedDecimalSeparator = true;
                    fFieldStart = result.length();
                }
                result.append((i < digitList.count) ? (char)(digitList.digits[i] + zeroDelta) : zero);
            }
            if (decimalSeparatorAlwaysShown && totalDigits == integerDigits) {
                iFieldEnd = result.length();
                result.append(decimal);
                addedDecimalSeparator = true;
                fFieldStart = result.length();
            }
            if (iFieldEnd == -1) {
                iFieldEnd = result.length();
            }
            delegate.formatted(INTEGER_FIELD, NumberFormat$Field.INTEGER, NumberFormat$Field.INTEGER, iFieldStart, iFieldEnd, result);
            if (addedDecimalSeparator) {
                delegate.formatted(NumberFormat$Field.DECIMAL_SEPARATOR, NumberFormat$Field.DECIMAL_SEPARATOR, iFieldEnd, fFieldStart, result);
            }
            if (fFieldStart == -1) {
                fFieldStart = result.length();
            }
            delegate.formatted(FRACTION_FIELD, NumberFormat$Field.FRACTION, NumberFormat$Field.FRACTION, fFieldStart, result.length(), result);
            int fieldStart = result.length();
            result.append(symbols.getExponentialSymbol());
            delegate.formatted(NumberFormat$Field.EXPONENT_SYMBOL, NumberFormat$Field.EXPONENT_SYMBOL, fieldStart, result.length(), result);
            if (digitList.isZero()) {
                exponent = 0;
            }
            boolean negativeExponent = exponent < 0;
            if (negativeExponent) {
                exponent = -exponent;
                fieldStart = result.length();
                result.append(symbols.getMinusSign());
                delegate.formatted(NumberFormat$Field.EXPONENT_SIGN, NumberFormat$Field.EXPONENT_SIGN, fieldStart, result.length(), result);
            }
            digitList.set(exponent);
            int eFieldStart = result.length();
            for (int i = digitList.decimalAt; i < minExponentDigits; ++i) {
                result.append(zero);
            }
            for (int i = 0; i < digitList.decimalAt; ++i) {
                result.append((i < digitList.count) ? (char)(digitList.digits[i] + zeroDelta) : zero);
            }
            delegate.formatted(NumberFormat$Field.EXPONENT, NumberFormat$Field.EXPONENT, eFieldStart, result.length(), result);
        } else {
            int iFieldStart = result.length();
            int count = minIntDigits;
            int digitIndex = 0;
            if (digitList.decimalAt > 0 && count < digitList.decimalAt) {
                count = digitList.decimalAt;
            }
            if (count > maxIntDigits) {
                count = maxIntDigits;
                digitIndex = digitList.decimalAt - count;
            }
            int sizeBeforeIntegerPart = result.length();
            for (int i = count - 1; i >= 0; --i) {
                if (i < digitList.decimalAt && digitIndex < digitList.count) {
                    result.append((char)(digitList.digits[digitIndex++] + zeroDelta));
                } else {
                    result.append(zero);
                }
                if (isGroupingUsed() && i > 0 && (groupingSize != 0) && (i % groupingSize == 0)) {
                    int gStart = result.length();
                    result.append(grouping);
                    delegate.formatted(NumberFormat$Field.GROUPING_SEPARATOR, NumberFormat$Field.GROUPING_SEPARATOR, gStart, result.length(), result);
                }
            }
            boolean fractionPresent = (minFraDigits > 0) || (!isInteger && digitIndex < digitList.count);
            if (!fractionPresent && result.length() == sizeBeforeIntegerPart) {
                result.append(zero);
            }
            delegate.formatted(INTEGER_FIELD, NumberFormat$Field.INTEGER, NumberFormat$Field.INTEGER, iFieldStart, result.length(), result);
            int sStart = result.length();
            if (decimalSeparatorAlwaysShown || fractionPresent) {
                result.append(decimal);
            }
            if (sStart != result.length()) {
                delegate.formatted(NumberFormat$Field.DECIMAL_SEPARATOR, NumberFormat$Field.DECIMAL_SEPARATOR, sStart, result.length(), result);
            }
            int fFieldStart = result.length();
            for (int i = 0; i < maxFraDigits; ++i) {
                if (i >= minFraDigits && (isInteger || digitIndex >= digitList.count)) {
                    break;
                }
                if (-1 - i > (digitList.decimalAt - 1)) {
                    result.append(zero);
                    continue;
                }
                if (!isInteger && digitIndex < digitList.count) {
                    result.append((char)(digitList.digits[digitIndex++] + zeroDelta));
                } else {
                    result.append(zero);
                }
            }
            delegate.formatted(FRACTION_FIELD, NumberFormat$Field.FRACTION, NumberFormat$Field.FRACTION, fFieldStart, result.length(), result);
        }
        if (isNegative) {
            append(result, negativeSuffix, delegate, getNegativeSuffixFieldPositions(), NumberFormat$Field.SIGN);
        } else {
            append(result, positiveSuffix, delegate, getPositiveSuffixFieldPositions(), NumberFormat$Field.SIGN);
        }
        return result;
    }
    
    private void append(StringBuffer result, String string, Format$FieldDelegate delegate, FieldPosition[] positions, Format$Field signAttribute) {
        int start = result.length();
        if (string.length() > 0) {
            result.append(string);
            for (int counter = 0, max = positions.length; counter < max; counter++) {
                FieldPosition fp = positions[counter];
                Format$Field attribute = fp.getFieldAttribute();
                if (attribute == NumberFormat$Field.SIGN) {
                    attribute = signAttribute;
                }
                delegate.formatted(attribute, attribute, start + fp.getBeginIndex(), start + fp.getEndIndex(), result);
            }
        }
    }
    
    public Number parse(String text, ParsePosition pos) {
        if (text.regionMatches(pos.index, symbols.getNaN(), 0, symbols.getNaN().length())) {
            pos.index = pos.index + symbols.getNaN().length();
            return new Double(Double.NaN);
        }
        boolean[] status = new boolean[STATUS_LENGTH];
        if (!subparse(text, pos, positivePrefix, negativePrefix, digitList, false, status)) {
            return null;
        }
        if (status[STATUS_INFINITE]) {
            if (status[STATUS_POSITIVE] == (multiplier >= 0)) {
                return new Double(Double.POSITIVE_INFINITY);
            } else {
                return new Double(Double.NEGATIVE_INFINITY);
            }
        }
        if (multiplier == 0) {
            if (digitList.isZero()) {
                return new Double(Double.NaN);
            } else if (status[STATUS_POSITIVE]) {
                return new Double(Double.POSITIVE_INFINITY);
            } else {
                return new Double(Double.NEGATIVE_INFINITY);
            }
        }
        if (isParseBigDecimal()) {
            BigDecimal bigDecimalResult = digitList.getBigDecimal();
            if (multiplier != 1) {
                try {
                    bigDecimalResult = bigDecimalResult.divide(getBigDecimalMultiplier());
                } catch (ArithmeticException e) {
                    bigDecimalResult = bigDecimalResult.divide(getBigDecimalMultiplier(), BigDecimal.ROUND_HALF_EVEN);
                }
            }
            if (!status[STATUS_POSITIVE]) {
                bigDecimalResult = bigDecimalResult.negate();
            }
            return bigDecimalResult;
        } else {
            boolean gotDouble = true;
            boolean gotLongMinimum = false;
            double doubleResult = 0.0;
            long longResult = 0;
            if (digitList.fitsIntoLong(status[STATUS_POSITIVE], isParseIntegerOnly())) {
                gotDouble = false;
                longResult = digitList.getLong();
                if (longResult < 0) {
                    gotLongMinimum = true;
                }
            } else {
                doubleResult = digitList.getDouble();
            }
            if (multiplier != 1) {
                if (gotDouble) {
                    doubleResult /= multiplier;
                } else {
                    if (longResult % multiplier == 0) {
                        longResult /= multiplier;
                    } else {
                        doubleResult = ((double)longResult) / multiplier;
                        gotDouble = true;
                    }
                }
            }
            if (!status[STATUS_POSITIVE] && !gotLongMinimum) {
                doubleResult = -doubleResult;
                longResult = -longResult;
            }
            if (multiplier != 1 && gotDouble) {
                longResult = (long)doubleResult;
                gotDouble = ((doubleResult != (double)longResult) || (doubleResult == 0.0 && 1 / doubleResult < 0.0)) && !isParseIntegerOnly();
            }
            return gotDouble ? (Number)new Double(doubleResult) : (Number)new Long(longResult);
        }
    }
    
    private BigInteger getBigIntegerMultiplier() {
        if (bigIntegerMultiplier == null) {
            bigIntegerMultiplier = BigInteger.valueOf(multiplier);
        }
        return bigIntegerMultiplier;
    }
    private transient BigInteger bigIntegerMultiplier;
    
    private BigDecimal getBigDecimalMultiplier() {
        if (bigDecimalMultiplier == null) {
            bigDecimalMultiplier = new BigDecimal(multiplier);
        }
        return bigDecimalMultiplier;
    }
    private transient BigDecimal bigDecimalMultiplier;
    private static final int STATUS_INFINITE = 0;
    private static final int STATUS_POSITIVE = 1;
    private static final int STATUS_LENGTH = 2;
    
    private final boolean subparse(String text, ParsePosition parsePosition, String positivePrefix, String negativePrefix, DigitList digits, boolean isExponent, boolean[] status) {
        int position = parsePosition.index;
        int oldStart = parsePosition.index;
        int backup;
        boolean gotPositive;
        boolean gotNegative;
        gotPositive = text.regionMatches(position, positivePrefix, 0, positivePrefix.length());
        gotNegative = text.regionMatches(position, negativePrefix, 0, negativePrefix.length());
        if (gotPositive && gotNegative) {
            if (positivePrefix.length() > negativePrefix.length()) {
                gotNegative = false;
            } else if (positivePrefix.length() < negativePrefix.length()) {
                gotPositive = false;
            }
        }
        if (gotPositive) {
            position += positivePrefix.length();
        } else if (gotNegative) {
            position += negativePrefix.length();
        } else {
            parsePosition.errorIndex = position;
            return false;
        }
        status[STATUS_INFINITE] = false;
        if (!isExponent && text.regionMatches(position, symbols.getInfinity(), 0, symbols.getInfinity().length())) {
            position += symbols.getInfinity().length();
            status[STATUS_INFINITE] = true;
        } else {
            digits.decimalAt = digits.count = 0;
            char zero = symbols.getZeroDigit();
            char decimal = isCurrencyFormat ? symbols.getMonetaryDecimalSeparator() : symbols.getDecimalSeparator();
            char grouping = symbols.getGroupingSeparator();
            char exponentChar = symbols.getExponentialSymbol();
            boolean sawDecimal = false;
            boolean sawExponent = false;
            boolean sawDigit = false;
            int exponent = 0;
            int digitCount = 0;
            backup = -1;
            for (; position < text.length(); ++position) {
                char ch = text.charAt(position);
                int digit = ch - zero;
                if (digit < 0 || digit > 9) {
                    digit = Character.digit(ch, 10);
                }
                if (digit == 0) {
                    backup = -1;
                    sawDigit = true;
                    if (digits.count == 0) {
                        if (!sawDecimal) {
                            continue;
                        }
                        --digits.decimalAt;
                    } else {
                        ++digitCount;
                        digits.append((char)(digit + '0'));
                    }
                } else if (digit > 0 && digit <= 9) {
                    sawDigit = true;
                    ++digitCount;
                    digits.append((char)(digit + '0'));
                    backup = -1;
                } else if (!isExponent && ch == decimal) {
                    if (isParseIntegerOnly() || sawDecimal) {
                        break;
                    }
                    digits.decimalAt = digitCount;
                    sawDecimal = true;
                } else if (!isExponent && ch == grouping && isGroupingUsed()) {
                    if (sawDecimal) {
                        break;
                    }
                    backup = position;
                } else if (!isExponent && ch == exponentChar && !sawExponent) {
                    ParsePosition pos = new ParsePosition(position + 1);
                    boolean[] stat = new boolean[STATUS_LENGTH];
                    DigitList exponentDigits = new DigitList();
                    if (subparse(text, pos, "", Character.toString(symbols.getMinusSign()), exponentDigits, true, stat) && exponentDigits.fitsIntoLong(stat[STATUS_POSITIVE], true)) {
                        position = pos.index;
                        exponent = (int)exponentDigits.getLong();
                        if (!stat[STATUS_POSITIVE]) {
                            exponent = -exponent;
                        }
                        sawExponent = true;
                    }
                    break;
                } else {
                    break;
                }
            }
            if (backup != -1) {
                position = backup;
            }
            if (!sawDecimal) {
                digits.decimalAt = digitCount;
            }
            digits.decimalAt += exponent;
            if (!sawDigit && digitCount == 0) {
                parsePosition.index = oldStart;
                parsePosition.errorIndex = oldStart;
                return false;
            }
        }
        if (!isExponent) {
            if (gotPositive) {
                gotPositive = text.regionMatches(position, positiveSuffix, 0, positiveSuffix.length());
            }
            if (gotNegative) {
                gotNegative = text.regionMatches(position, negativeSuffix, 0, negativeSuffix.length());
            }
            if (gotPositive && gotNegative) {
                if (positiveSuffix.length() > negativeSuffix.length()) {
                    gotNegative = false;
                } else if (positiveSuffix.length() < negativeSuffix.length()) {
                    gotPositive = false;
                }
            }
            if (gotPositive == gotNegative) {
                parsePosition.errorIndex = position;
                return false;
            }
            parsePosition.index = position + (gotPositive ? positiveSuffix.length() : negativeSuffix.length());
        } else {
            parsePosition.index = position;
        }
        status[STATUS_POSITIVE] = gotPositive;
        if (parsePosition.index == oldStart) {
            parsePosition.errorIndex = position;
            return false;
        }
        return true;
    }
    
    public DecimalFormatSymbols getDecimalFormatSymbols() {
        try {
            return (DecimalFormatSymbols)(DecimalFormatSymbols)symbols.clone();
        } catch (Exception foo) {
            return null;
        }
    }
    
    public void setDecimalFormatSymbols(DecimalFormatSymbols newSymbols) {
        try {
            symbols = (DecimalFormatSymbols)(DecimalFormatSymbols)newSymbols.clone();
            expandAffixes();
        } catch (Exception foo) {
        }
    }
    
    public String getPositivePrefix() {
        return positivePrefix;
    }
    
    public void setPositivePrefix(String newValue) {
        positivePrefix = newValue;
        posPrefixPattern = null;
        positivePrefixFieldPositions = null;
    }
    
    private FieldPosition[] getPositivePrefixFieldPositions() {
        if (positivePrefixFieldPositions == null) {
            if (posPrefixPattern != null) {
                positivePrefixFieldPositions = expandAffix(posPrefixPattern);
            } else {
                positivePrefixFieldPositions = EmptyFieldPositionArray;
            }
        }
        return positivePrefixFieldPositions;
    }
    
    public String getNegativePrefix() {
        return negativePrefix;
    }
    
    public void setNegativePrefix(String newValue) {
        negativePrefix = newValue;
        negPrefixPattern = null;
    }
    
    private FieldPosition[] getNegativePrefixFieldPositions() {
        if (negativePrefixFieldPositions == null) {
            if (negPrefixPattern != null) {
                negativePrefixFieldPositions = expandAffix(negPrefixPattern);
            } else {
                negativePrefixFieldPositions = EmptyFieldPositionArray;
            }
        }
        return negativePrefixFieldPositions;
    }
    
    public String getPositiveSuffix() {
        return positiveSuffix;
    }
    
    public void setPositiveSuffix(String newValue) {
        positiveSuffix = newValue;
        posSuffixPattern = null;
    }
    
    private FieldPosition[] getPositiveSuffixFieldPositions() {
        if (positiveSuffixFieldPositions == null) {
            if (posSuffixPattern != null) {
                positiveSuffixFieldPositions = expandAffix(posSuffixPattern);
            } else {
                positiveSuffixFieldPositions = EmptyFieldPositionArray;
            }
        }
        return positiveSuffixFieldPositions;
    }
    
    public String getNegativeSuffix() {
        return negativeSuffix;
    }
    
    public void setNegativeSuffix(String newValue) {
        negativeSuffix = newValue;
        negSuffixPattern = null;
    }
    
    private FieldPosition[] getNegativeSuffixFieldPositions() {
        if (negativeSuffixFieldPositions == null) {
            if (negSuffixPattern != null) {
                negativeSuffixFieldPositions = expandAffix(negSuffixPattern);
            } else {
                negativeSuffixFieldPositions = EmptyFieldPositionArray;
            }
        }
        return negativeSuffixFieldPositions;
    }
    
    public int getMultiplier() {
        return multiplier;
    }
    
    public void setMultiplier(int newValue) {
        multiplier = newValue;
        bigDecimalMultiplier = null;
        bigIntegerMultiplier = null;
    }
    
    public int getGroupingSize() {
        return groupingSize;
    }
    
    public void setGroupingSize(int newValue) {
        groupingSize = (byte)newValue;
    }
    
    public boolean isDecimalSeparatorAlwaysShown() {
        return decimalSeparatorAlwaysShown;
    }
    
    public void setDecimalSeparatorAlwaysShown(boolean newValue) {
        decimalSeparatorAlwaysShown = newValue;
    }
    
    public boolean isParseBigDecimal() {
        return parseBigDecimal;
    }
    
    public void setParseBigDecimal(boolean newValue) {
        parseBigDecimal = newValue;
    }
    
    public Object clone() {
        try {
            DecimalFormat other = (DecimalFormat)(DecimalFormat)super.clone();
            other.symbols = (DecimalFormatSymbols)(DecimalFormatSymbols)symbols.clone();
            other.digitList = (DigitList)(DigitList)digitList.clone();
            return other;
        } catch (Exception e) {
            throw new InternalError();
        }
    }
    
    public boolean equals(Object obj) {
        if (obj == null) return false;
        if (!super.equals(obj)) return false;
        DecimalFormat other = (DecimalFormat)(DecimalFormat)obj;
        return ((posPrefixPattern == other.posPrefixPattern && positivePrefix.equals(other.positivePrefix)) || (posPrefixPattern != null && posPrefixPattern.equals(other.posPrefixPattern))) && ((posSuffixPattern == other.posSuffixPattern && positiveSuffix.equals(other.positiveSuffix)) || (posSuffixPattern != null && posSuffixPattern.equals(other.posSuffixPattern))) && ((negPrefixPattern == other.negPrefixPattern && negativePrefix.equals(other.negativePrefix)) || (negPrefixPattern != null && negPrefixPattern.equals(other.negPrefixPattern))) && ((negSuffixPattern == other.negSuffixPattern && negativeSuffix.equals(other.negativeSuffix)) || (negSuffixPattern != null && negSuffixPattern.equals(other.negSuffixPattern))) && multiplier == other.multiplier && groupingSize == other.groupingSize && decimalSeparatorAlwaysShown == other.decimalSeparatorAlwaysShown && parseBigDecimal == other.parseBigDecimal && useExponentialNotation == other.useExponentialNotation && (!useExponentialNotation || minExponentDigits == other.minExponentDigits) && maximumIntegerDigits == other.maximumIntegerDigits && minimumIntegerDigits == other.minimumIntegerDigits && maximumFractionDigits == other.maximumFractionDigits && minimumFractionDigits == other.minimumFractionDigits && symbols.equals(other.symbols);
    }
    
    public int hashCode() {
        return super.hashCode() * 37 + positivePrefix.hashCode();
    }
    
    public String toPattern() {
        return toPattern(false);
    }
    
    public String toLocalizedPattern() {
        return toPattern(true);
    }
    
    private void expandAffixes() {
        StringBuffer buffer = new StringBuffer();
        if (posPrefixPattern != null) {
            positivePrefix = expandAffix(posPrefixPattern, buffer);
            positivePrefixFieldPositions = null;
        }
        if (posSuffixPattern != null) {
            positiveSuffix = expandAffix(posSuffixPattern, buffer);
            positiveSuffixFieldPositions = null;
        }
        if (negPrefixPattern != null) {
            negativePrefix = expandAffix(negPrefixPattern, buffer);
            negativePrefixFieldPositions = null;
        }
        if (negSuffixPattern != null) {
            negativeSuffix = expandAffix(negSuffixPattern, buffer);
            negativeSuffixFieldPositions = null;
        }
    }
    
    private String expandAffix(String pattern, StringBuffer buffer) {
        buffer.setLength(0);
        for (int i = 0; i < pattern.length(); ) {
            char c = pattern.charAt(i++);
            if (c == QUOTE) {
                c = pattern.charAt(i++);
                switch (c) {
                case CURRENCY_SIGN: 
                    if (i < pattern.length() && pattern.charAt(i) == CURRENCY_SIGN) {
                        ++i;
                        buffer.append(symbols.getInternationalCurrencySymbol());
                    } else {
                        buffer.append(symbols.getCurrencySymbol());
                    }
                    continue;
                
                case PATTERN_PERCENT: 
                    c = symbols.getPercent();
                    break;
                
                case PATTERN_PER_MILLE: 
                    c = symbols.getPerMill();
                    break;
                
                case PATTERN_MINUS: 
                    c = symbols.getMinusSign();
                    break;
                
                }
            }
            buffer.append(c);
        }
        return buffer.toString();
    }
    
    private FieldPosition[] expandAffix(String pattern) {
        ArrayList positions = null;
        int stringIndex = 0;
        for (int i = 0; i < pattern.length(); ) {
            char c = pattern.charAt(i++);
            if (c == QUOTE) {
                int field = -1;
                Format$Field fieldID = null;
                c = pattern.charAt(i++);
                switch (c) {
                case CURRENCY_SIGN: 
                    String string;
                    if (i < pattern.length() && pattern.charAt(i) == CURRENCY_SIGN) {
                        ++i;
                        string = symbols.getInternationalCurrencySymbol();
                    } else {
                        string = symbols.getCurrencySymbol();
                    }
                    if (string.length() > 0) {
                        if (positions == null) {
                            positions = new ArrayList(2);
                        }
                        FieldPosition fp = new FieldPosition(NumberFormat$Field.CURRENCY);
                        fp.setBeginIndex(stringIndex);
                        fp.setEndIndex(stringIndex + string.length());
                        positions.add(fp);
                        stringIndex += string.length();
                    }
                    continue;
                
                case PATTERN_PERCENT: 
                    c = symbols.getPercent();
                    field = -1;
                    fieldID = NumberFormat$Field.PERCENT;
                    break;
                
                case PATTERN_PER_MILLE: 
                    c = symbols.getPerMill();
                    field = -1;
                    fieldID = NumberFormat$Field.PERMILLE;
                    break;
                
                case PATTERN_MINUS: 
                    c = symbols.getMinusSign();
                    field = -1;
                    fieldID = NumberFormat$Field.SIGN;
                    break;
                
                }
                if (fieldID != null) {
                    if (positions == null) {
                        positions = new ArrayList(2);
                    }
                    FieldPosition fp = new FieldPosition(fieldID, field);
                    fp.setBeginIndex(stringIndex);
                    fp.setEndIndex(stringIndex + 1);
                    positions.add(fp);
                }
            }
            stringIndex++;
        }
        if (positions != null) {
            return (FieldPosition[])(FieldPosition[])positions.toArray(EmptyFieldPositionArray);
        }
        return EmptyFieldPositionArray;
    }
    
    private void appendAffix(StringBuffer buffer, String affixPattern, String expAffix, boolean localized) {
        if (affixPattern == null) {
            appendAffix(buffer, expAffix, localized);
        } else {
            int i;
            for (int pos = 0; pos < affixPattern.length(); pos = i) {
                i = affixPattern.indexOf(QUOTE, pos);
                if (i < 0) {
                    appendAffix(buffer, affixPattern.substring(pos), localized);
                    break;
                }
                if (i > pos) {
                    appendAffix(buffer, affixPattern.substring(pos, i), localized);
                }
                char c = affixPattern.charAt(++i);
                ++i;
                if (c == QUOTE) {
                    buffer.append(c);
                } else if (c == CURRENCY_SIGN && i < affixPattern.length() && affixPattern.charAt(i) == CURRENCY_SIGN) {
                    ++i;
                    buffer.append(c);
                } else if (localized) {
                    switch (c) {
                    case PATTERN_PERCENT: 
                        c = symbols.getPercent();
                        break;
                    
                    case PATTERN_PER_MILLE: 
                        c = symbols.getPerMill();
                        break;
                    
                    case PATTERN_MINUS: 
                        c = symbols.getMinusSign();
                        break;
                    
                    }
                }
                buffer.append(c);
            }
        }
    }
    
    private void appendAffix(StringBuffer buffer, String affix, boolean localized) {
        boolean needQuote;
        if (localized) {
            needQuote = affix.indexOf(symbols.getZeroDigit()) >= 0 || affix.indexOf(symbols.getGroupingSeparator()) >= 0 || affix.indexOf(symbols.getDecimalSeparator()) >= 0 || affix.indexOf(symbols.getPercent()) >= 0 || affix.indexOf(symbols.getPerMill()) >= 0 || affix.indexOf(symbols.getDigit()) >= 0 || affix.indexOf(symbols.getPatternSeparator()) >= 0 || affix.indexOf(symbols.getMinusSign()) >= 0 || affix.indexOf(CURRENCY_SIGN) >= 0;
        } else {
            needQuote = affix.indexOf(PATTERN_ZERO_DIGIT) >= 0 || affix.indexOf(PATTERN_GROUPING_SEPARATOR) >= 0 || affix.indexOf(PATTERN_DECIMAL_SEPARATOR) >= 0 || affix.indexOf(PATTERN_PERCENT) >= 0 || affix.indexOf(PATTERN_PER_MILLE) >= 0 || affix.indexOf(PATTERN_DIGIT) >= 0 || affix.indexOf(PATTERN_SEPARATOR) >= 0 || affix.indexOf(PATTERN_MINUS) >= 0 || affix.indexOf(CURRENCY_SIGN) >= 0;
        }
        if (needQuote) buffer.append('\'');
        if (affix.indexOf('\'') < 0) buffer.append(affix); else {
            for (int j = 0; j < affix.length(); ++j) {
                char c = affix.charAt(j);
                buffer.append(c);
                if (c == '\'') buffer.append(c);
            }
        }
        if (needQuote) buffer.append('\'');
    }
    
    private String toPattern(boolean localized) {
        StringBuffer result = new StringBuffer();
        for (int j = 1; j >= 0; --j) {
            if (j == 1) appendAffix(result, posPrefixPattern, positivePrefix, localized); else appendAffix(result, negPrefixPattern, negativePrefix, localized);
            int i;
            int digitCount = useExponentialNotation ? getMaximumIntegerDigits() : Math.max(groupingSize, getMinimumIntegerDigits()) + 1;
            for (i = digitCount; i > 0; --i) {
                if (i != digitCount && isGroupingUsed() && groupingSize != 0 && i % groupingSize == 0) {
                    result.append(localized ? symbols.getGroupingSeparator() : PATTERN_GROUPING_SEPARATOR);
                }
                result.append(i <= getMinimumIntegerDigits() ? (localized ? symbols.getZeroDigit() : PATTERN_ZERO_DIGIT) : (localized ? symbols.getDigit() : PATTERN_DIGIT));
            }
            if (getMaximumFractionDigits() > 0 || decimalSeparatorAlwaysShown) result.append(localized ? symbols.getDecimalSeparator() : PATTERN_DECIMAL_SEPARATOR);
            for (i = 0; i < getMaximumFractionDigits(); ++i) {
                if (i < getMinimumFractionDigits()) {
                    result.append(localized ? symbols.getZeroDigit() : PATTERN_ZERO_DIGIT);
                } else {
                    result.append(localized ? symbols.getDigit() : PATTERN_DIGIT);
                }
            }
            if (useExponentialNotation) {
                result.append(localized ? symbols.getExponentialSymbol() : PATTERN_EXPONENT);
                for (i = 0; i < minExponentDigits; ++i) result.append(localized ? symbols.getZeroDigit() : PATTERN_ZERO_DIGIT);
            }
            if (j == 1) {
                appendAffix(result, posSuffixPattern, positiveSuffix, localized);
                if ((negSuffixPattern == posSuffixPattern && negativeSuffix.equals(positiveSuffix)) || (negSuffixPattern != null && negSuffixPattern.equals(posSuffixPattern))) {
                    if ((negPrefixPattern != null && posPrefixPattern != null && negPrefixPattern.equals("\'-" + posPrefixPattern)) || (negPrefixPattern == posPrefixPattern && negativePrefix.equals(symbols.getMinusSign() + positivePrefix))) break;
                }
                result.append(localized ? symbols.getPatternSeparator() : PATTERN_SEPARATOR);
            } else appendAffix(result, negSuffixPattern, negativeSuffix, localized);
        }
        return result.toString();
    }
    
    public void applyPattern(String pattern) {
        applyPattern(pattern, false);
    }
    
    public void applyLocalizedPattern(String pattern) {
        applyPattern(pattern, true);
    }
    
    private void applyPattern(String pattern, boolean localized) {
        char zeroDigit = PATTERN_ZERO_DIGIT;
        char groupingSeparator = PATTERN_GROUPING_SEPARATOR;
        char decimalSeparator = PATTERN_DECIMAL_SEPARATOR;
        char percent = PATTERN_PERCENT;
        char perMill = PATTERN_PER_MILLE;
        char digit = PATTERN_DIGIT;
        char separator = PATTERN_SEPARATOR;
        char exponent = PATTERN_EXPONENT;
        char minus = PATTERN_MINUS;
        if (localized) {
            zeroDigit = symbols.getZeroDigit();
            groupingSeparator = symbols.getGroupingSeparator();
            decimalSeparator = symbols.getDecimalSeparator();
            percent = symbols.getPercent();
            perMill = symbols.getPerMill();
            digit = symbols.getDigit();
            separator = symbols.getPatternSeparator();
            exponent = symbols.getExponentialSymbol();
            minus = symbols.getMinusSign();
        }
        boolean gotNegative = false;
        decimalSeparatorAlwaysShown = false;
        isCurrencyFormat = false;
        useExponentialNotation = false;
        int phaseOneStart = 0;
        int phaseOneLength = 0;
        int start = 0;
        for (int j = 1; j >= 0 && start < pattern.length(); --j) {
            boolean inQuote = false;
            StringBuffer prefix = new StringBuffer();
            StringBuffer suffix = new StringBuffer();
            int decimalPos = -1;
            int multiplier = 1;
            int digitLeftCount = 0;
            int zeroDigitCount = 0;
            int digitRightCount = 0;
            byte groupingCount = -1;
            int phase = 0;
            StringBuffer affix = prefix;
            for (int pos = start; pos < pattern.length(); ++pos) {
                char ch = pattern.charAt(pos);
                switch (phase) {
                case 0: 
                
                case 2: 
                    if (inQuote) {
                        if (ch == QUOTE) {
                            if ((pos + 1) < pattern.length() && pattern.charAt(pos + 1) == QUOTE) {
                                ++pos;
                                affix.append("\'\'");
                            } else {
                                inQuote = false;
                            }
                            continue;
                        }
                    } else {
                        if (ch == digit || ch == zeroDigit || ch == groupingSeparator || ch == decimalSeparator) {
                            phase = 1;
                            if (j == 1) {
                                phaseOneStart = pos;
                            }
                            --pos;
                            continue;
                        } else if (ch == CURRENCY_SIGN) {
                            boolean doubled = (pos + 1) < pattern.length() && pattern.charAt(pos + 1) == CURRENCY_SIGN;
                            if (doubled) {
                                ++pos;
                            }
                            isCurrencyFormat = true;
                            affix.append(doubled ? "\'\244\244" : "\'\244");
                            continue;
                        } else if (ch == QUOTE) {
                            if (ch == QUOTE) {
                                if ((pos + 1) < pattern.length() && pattern.charAt(pos + 1) == QUOTE) {
                                    ++pos;
                                    affix.append("\'\'");
                                } else {
                                    inQuote = true;
                                }
                                continue;
                            }
                        } else if (ch == separator) {
                            if (phase == 0 || j == 0) {
                                throw new IllegalArgumentException("Unquoted special character \'" + ch + "\' in pattern \"" + pattern + '\"');
                            }
                            start = pos + 1;
                            pos = pattern.length();
                            continue;
                        } else if (ch == percent) {
                            if (multiplier != 1) {
                                throw new IllegalArgumentException("Too many percent/per mille characters in pattern \"" + pattern + '\"');
                            }
                            multiplier = 100;
                            affix.append("\'%");
                            continue;
                        } else if (ch == perMill) {
                            if (multiplier != 1) {
                                throw new IllegalArgumentException("Too many percent/per mille characters in pattern \"" + pattern + '\"');
                            }
                            multiplier = 1000;
                            affix.append("\'\u2030");
                            continue;
                        } else if (ch == minus) {
                            affix.append("\'-");
                            continue;
                        }
                    }
                    affix.append(ch);
                    break;
                
                case 1: 
                    if (j == 1) {
                        ++phaseOneLength;
                    } else {
                        if (--phaseOneLength == 0) {
                            phase = 2;
                            affix = suffix;
                        }
                        continue;
                    }
                    if (ch == digit) {
                        if (zeroDigitCount > 0) {
                            ++digitRightCount;
                        } else {
                            ++digitLeftCount;
                        }
                        if (groupingCount >= 0 && decimalPos < 0) {
                            ++groupingCount;
                        }
                    } else if (ch == zeroDigit) {
                        if (digitRightCount > 0) {
                            throw new IllegalArgumentException("Unexpected \'0\' in pattern \"" + pattern + '\"');
                        }
                        ++zeroDigitCount;
                        if (groupingCount >= 0 && decimalPos < 0) {
                            ++groupingCount;
                        }
                    } else if (ch == groupingSeparator) {
                        groupingCount = 0;
                    } else if (ch == decimalSeparator) {
                        if (decimalPos >= 0) {
                            throw new IllegalArgumentException("Multiple decimal separators in pattern \"" + pattern + '\"');
                        }
                        decimalPos = digitLeftCount + zeroDigitCount + digitRightCount;
                    } else if (ch == exponent) {
                        if (useExponentialNotation) {
                            throw new IllegalArgumentException("Multiple exponential " + "symbols in pattern \"" + pattern + '\"');
                        }
                        useExponentialNotation = true;
                        minExponentDigits = 0;
                        while (++pos < pattern.length() && pattern.charAt(pos) == zeroDigit) {
                            ++minExponentDigits;
                            ++phaseOneLength;
                        }
                        if ((digitLeftCount + zeroDigitCount) < 1 || minExponentDigits < 1) {
                            throw new IllegalArgumentException("Malformed exponential " + "pattern \"" + pattern + '\"');
                        }
                        phase = 2;
                        affix = suffix;
                        --pos;
                        continue;
                    } else {
                        phase = 2;
                        affix = suffix;
                        --pos;
                        --phaseOneLength;
                        continue;
                    }
                    break;
                
                }
            }
            if (zeroDigitCount == 0 && digitLeftCount > 0 && decimalPos >= 0) {
                int n = decimalPos;
                if (n == 0) {
                    ++n;
                }
                digitRightCount = digitLeftCount - n;
                digitLeftCount = n - 1;
                zeroDigitCount = 1;
            }
            if ((decimalPos < 0 && digitRightCount > 0) || (decimalPos >= 0 && (decimalPos < digitLeftCount || decimalPos > (digitLeftCount + zeroDigitCount))) || groupingCount == 0 || inQuote) {
                throw new IllegalArgumentException("Malformed pattern \"" + pattern + '\"');
            }
            if (j == 1) {
                posPrefixPattern = prefix.toString();
                posSuffixPattern = suffix.toString();
                negPrefixPattern = posPrefixPattern;
                negSuffixPattern = posSuffixPattern;
                int digitTotalCount = digitLeftCount + zeroDigitCount + digitRightCount;
                int effectiveDecimalPos = decimalPos >= 0 ? decimalPos : digitTotalCount;
                setMinimumIntegerDigits(effectiveDecimalPos - digitLeftCount);
                setMaximumIntegerDigits(useExponentialNotation ? digitLeftCount + getMinimumIntegerDigits() : MAXIMUM_INTEGER_DIGITS);
                setMaximumFractionDigits(decimalPos >= 0 ? (digitTotalCount - decimalPos) : 0);
                setMinimumFractionDigits(decimalPos >= 0 ? (digitLeftCount + zeroDigitCount - decimalPos) : 0);
                setGroupingUsed(groupingCount > 0);
                this.groupingSize = (groupingCount > 0) ? groupingCount : 0;
                this.multiplier = multiplier;
                setDecimalSeparatorAlwaysShown(decimalPos == 0 || decimalPos == digitTotalCount);
            } else {
                negPrefixPattern = prefix.toString();
                negSuffixPattern = suffix.toString();
                gotNegative = true;
            }
        }
        if (pattern.length() == 0) {
            posPrefixPattern = posSuffixPattern = "";
            setMinimumIntegerDigits(0);
            setMaximumIntegerDigits(MAXIMUM_INTEGER_DIGITS);
            setMinimumFractionDigits(0);
            setMaximumFractionDigits(MAXIMUM_FRACTION_DIGITS);
        }
        if (!gotNegative || (negPrefixPattern.equals(posPrefixPattern) && negSuffixPattern.equals(posSuffixPattern))) {
            negSuffixPattern = posSuffixPattern;
            negPrefixPattern = "\'-" + posPrefixPattern;
        }
        expandAffixes();
    }
    
    public void setMaximumIntegerDigits(int newValue) {
        maximumIntegerDigits = Math.min(Math.max(0, newValue), MAXIMUM_INTEGER_DIGITS);
        super.setMaximumIntegerDigits((maximumIntegerDigits > DOUBLE_INTEGER_DIGITS) ? DOUBLE_INTEGER_DIGITS : maximumIntegerDigits);
        if (minimumIntegerDigits > maximumIntegerDigits) {
            minimumIntegerDigits = maximumIntegerDigits;
            super.setMinimumIntegerDigits((minimumIntegerDigits > DOUBLE_INTEGER_DIGITS) ? DOUBLE_INTEGER_DIGITS : minimumIntegerDigits);
        }
    }
    
    public void setMinimumIntegerDigits(int newValue) {
        minimumIntegerDigits = Math.min(Math.max(0, newValue), MAXIMUM_INTEGER_DIGITS);
        super.setMinimumIntegerDigits((minimumIntegerDigits > DOUBLE_INTEGER_DIGITS) ? DOUBLE_INTEGER_DIGITS : minimumIntegerDigits);
        if (minimumIntegerDigits > maximumIntegerDigits) {
            maximumIntegerDigits = minimumIntegerDigits;
            super.setMaximumIntegerDigits((maximumIntegerDigits > DOUBLE_INTEGER_DIGITS) ? DOUBLE_INTEGER_DIGITS : maximumIntegerDigits);
        }
    }
    
    public void setMaximumFractionDigits(int newValue) {
        maximumFractionDigits = Math.min(Math.max(0, newValue), MAXIMUM_FRACTION_DIGITS);
        super.setMaximumFractionDigits((maximumFractionDigits > DOUBLE_FRACTION_DIGITS) ? DOUBLE_FRACTION_DIGITS : maximumFractionDigits);
        if (minimumFractionDigits > maximumFractionDigits) {
            minimumFractionDigits = maximumFractionDigits;
            super.setMinimumFractionDigits((minimumFractionDigits > DOUBLE_FRACTION_DIGITS) ? DOUBLE_FRACTION_DIGITS : minimumFractionDigits);
        }
    }
    
    public void setMinimumFractionDigits(int newValue) {
        minimumFractionDigits = Math.min(Math.max(0, newValue), MAXIMUM_FRACTION_DIGITS);
        super.setMinimumFractionDigits((minimumFractionDigits > DOUBLE_FRACTION_DIGITS) ? DOUBLE_FRACTION_DIGITS : minimumFractionDigits);
        if (minimumFractionDigits > maximumFractionDigits) {
            maximumFractionDigits = minimumFractionDigits;
            super.setMaximumFractionDigits((maximumFractionDigits > DOUBLE_FRACTION_DIGITS) ? DOUBLE_FRACTION_DIGITS : maximumFractionDigits);
        }
    }
    
    public int getMaximumIntegerDigits() {
        return maximumIntegerDigits;
    }
    
    public int getMinimumIntegerDigits() {
        return minimumIntegerDigits;
    }
    
    public int getMaximumFractionDigits() {
        return maximumFractionDigits;
    }
    
    public int getMinimumFractionDigits() {
        return minimumFractionDigits;
    }
    
    public Currency getCurrency() {
        return symbols.getCurrency();
    }
    
    public void setCurrency(Currency currency) {
        if (currency != symbols.getCurrency()) {
            symbols.setCurrency(currency);
            if (isCurrencyFormat) {
                expandAffixes();
            }
        }
    }
    
    void adjustForCurrencyDefaultFractionDigits() {
        Currency currency = symbols.getCurrency();
        if (currency == null) {
            try {
                currency = Currency.getInstance(symbols.getInternationalCurrencySymbol());
            } catch (IllegalArgumentException e) {
            }
        }
        if (currency != null) {
            int digits = currency.getDefaultFractionDigits();
            if (digits != -1) {
                int oldMinDigits = getMinimumFractionDigits();
                if (oldMinDigits == getMaximumFractionDigits()) {
                    setMinimumFractionDigits(digits);
                    setMaximumFractionDigits(digits);
                } else {
                    setMinimumFractionDigits(Math.min(digits, oldMinDigits));
                    setMaximumFractionDigits(digits);
                }
            }
        }
    }
    
    private void readObject(ObjectInputStream stream) throws IOException, ClassNotFoundException {
        stream.defaultReadObject();
        if (super.getMaximumIntegerDigits() > DOUBLE_INTEGER_DIGITS || super.getMaximumFractionDigits() > DOUBLE_FRACTION_DIGITS) {
            throw new InvalidObjectException("Digit count out of range");
        }
        if (serialVersionOnStream < 3) {
            setMaximumIntegerDigits(super.getMaximumIntegerDigits());
            setMinimumIntegerDigits(super.getMinimumIntegerDigits());
            setMaximumFractionDigits(super.getMaximumFractionDigits());
            setMinimumFractionDigits(super.getMinimumFractionDigits());
        }
        if (serialVersionOnStream < 1) {
            useExponentialNotation = false;
        }
        serialVersionOnStream = currentSerialVersion;
        digitList = new DigitList();
    }
    private transient DigitList digitList = new DigitList();
    private String positivePrefix = "";
    private String positiveSuffix = "";
    private String negativePrefix = "-";
    private String negativeSuffix = "";
    private String posPrefixPattern;
    private String posSuffixPattern;
    private String negPrefixPattern;
    private String negSuffixPattern;
    private int multiplier = 1;
    private byte groupingSize = 3;
    private boolean decimalSeparatorAlwaysShown = false;
    private boolean parseBigDecimal = false;
    private transient boolean isCurrencyFormat = false;
    private DecimalFormatSymbols symbols = null;
    private boolean useExponentialNotation;
    private transient FieldPosition[] positivePrefixFieldPositions;
    private transient FieldPosition[] positiveSuffixFieldPositions;
    private transient FieldPosition[] negativePrefixFieldPositions;
    private transient FieldPosition[] negativeSuffixFieldPositions;
    private byte minExponentDigits;
    private int maximumIntegerDigits = super.getMaximumIntegerDigits();
    private int minimumIntegerDigits = super.getMinimumIntegerDigits();
    private int maximumFractionDigits = super.getMaximumFractionDigits();
    private int minimumFractionDigits = super.getMinimumFractionDigits();
    static final int currentSerialVersion = 3;
    private int serialVersionOnStream = currentSerialVersion;
    private static final char PATTERN_ZERO_DIGIT = '0';
    private static final char PATTERN_GROUPING_SEPARATOR = ',';
    private static final char PATTERN_DECIMAL_SEPARATOR = '.';
    private static final char PATTERN_PER_MILLE = '\u2030';
    private static final char PATTERN_PERCENT = '%';
    private static final char PATTERN_DIGIT = '#';
    private static final char PATTERN_SEPARATOR = ';';
    private static final char PATTERN_EXPONENT = 'E';
    private static final char PATTERN_MINUS = '-';
    private static final char CURRENCY_SIGN = '\244';
    private static final char QUOTE = '\'';
    private static FieldPosition[] EmptyFieldPositionArray = new FieldPosition[0];
    static final int DOUBLE_INTEGER_DIGITS = 309;
    static final int DOUBLE_FRACTION_DIGITS = 340;
    static final int MAXIMUM_INTEGER_DIGITS = Integer.MAX_VALUE;
    static final int MAXIMUM_FRACTION_DIGITS = Integer.MAX_VALUE;
    static final long serialVersionUID = 864413376551465018L;
    private static Hashtable cachedLocaleData = new Hashtable(3);
}
