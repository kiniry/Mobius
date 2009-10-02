package java.util;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;
import java.text.DateFormatSymbols;
import java.text.DecimalFormat;
import java.text.DecimalFormatSymbols;
import java.text.NumberFormat;
import java.util.Calendar;
import java.util.Date;
import java.util.Locale;
import sun.misc.FpUtils;
import sun.misc.DoubleConsts;
import sun.misc.FormattedFloatingDecimal;

class Formatter$FormatSpecifier implements Formatter$FormatString {
    /*synthetic*/ final Formatter this$0;
    /*synthetic*/ static final boolean $assertionsDisabled = !Formatter.class.desiredAssertionStatus();
    private int index = -1;
    private Formatter$Flags f = Formatter$Flags.NONE;
    private int width;
    private int precision;
    private boolean dt = false;
    private char c;
    private Formatter formatter;
    private String ls;
    
    private int index(String s) {
        if (s != null) {
            try {
                index = Integer.parseInt(s.substring(0, s.length() - 1));
            } catch (NumberFormatException x) {
                if (!$assertionsDisabled) throw new AssertionError();
            }
        } else {
            index = 0;
        }
        return index;
    }
    
    public int index() {
        return index;
    }
    
    private Formatter$Flags flags(String s) {
        f = Formatter$Flags.parse(s);
        if (f.contains(Formatter$Flags.PREVIOUS)) index = -1;
        return f;
    }
    
    Formatter$Flags flags() {
        return f;
    }
    
    private int width(String s) {
        width = -1;
        if (s != null) {
            try {
                width = Integer.parseInt(s);
                if (width < 0) throw new IllegalFormatWidthException(width);
            } catch (NumberFormatException x) {
                if (!$assertionsDisabled) throw new AssertionError();
            }
        }
        return width;
    }
    
    int width() {
        return width;
    }
    
    private int precision(String s) {
        precision = -1;
        if (s != null) {
            try {
                precision = Integer.parseInt(s.substring(1));
                if (precision < 0) throw new IllegalFormatPrecisionException(precision);
            } catch (NumberFormatException x) {
                if (!$assertionsDisabled) throw new AssertionError();
            }
        }
        return precision;
    }
    
    int precision() {
        return precision;
    }
    
    private char conversion(String s) {
        c = s.charAt(0);
        if (!dt) {
            if (!Formatter$Conversion.isValid(c)) throw new UnknownFormatConversionException(String.valueOf(c));
            if (Character.isUpperCase(c)) Formatter.Flags.access$100(f, Formatter$Flags.UPPERCASE);
            c = Character.toLowerCase(c);
            if (Formatter$Conversion.isText(c)) index = -2;
        }
        return c;
    }
    
    private char conversion() {
        return c;
    }
    
    Formatter$FormatSpecifier(/*synthetic*/ final Formatter this$0, Formatter formatter, String[] sa) {
        this.this$0 = this$0;
        
        this.formatter = formatter;
        int idx = 0;
        index(sa[idx++]);
        flags(sa[idx++]);
        width(sa[idx++]);
        precision(sa[idx++]);
        if (sa[idx] != null) {
            dt = true;
            if (sa[idx].equals("T")) Formatter.Flags.access$100(f, Formatter$Flags.UPPERCASE);
        }
        conversion(sa[++idx]);
        if (dt) checkDateTime(); else if (Formatter$Conversion.isGeneral(c)) checkGeneral(); else if (c == Formatter$Conversion.CHARACTER) checkCharacter(); else if (Formatter$Conversion.isInteger(c)) checkInteger(); else if (Formatter$Conversion.isFloat(c)) checkFloat(); else if (Formatter$Conversion.isText(c)) checkText(); else throw new UnknownFormatConversionException(String.valueOf(c));
    }
    
    public void print(Object arg, Locale l) throws IOException {
        if (dt) {
            printDateTime(arg, l);
            return;
        }
        switch (c) {
        case Formatter$Conversion.DECIMAL_INTEGER: 
        
        case Formatter$Conversion.OCTAL_INTEGER: 
        
        case Formatter$Conversion.HEXADECIMAL_INTEGER: 
            printInteger(arg, l);
            break;
        
        case Formatter$Conversion.SCIENTIFIC: 
        
        case Formatter$Conversion.GENERAL: 
        
        case Formatter$Conversion.DECIMAL_FLOAT: 
        
        case Formatter$Conversion.HEXADECIMAL_FLOAT: 
            printFloat(arg, l);
            break;
        
        case Formatter$Conversion.CHARACTER: 
            printCharacter(arg);
            break;
        
        case Formatter$Conversion.BOOLEAN: 
            printBoolean(arg);
            break;
        
        case Formatter$Conversion.STRING: 
            printString(arg, l);
            break;
        
        case Formatter$Conversion.HASHCODE: 
            printHashCode(arg);
            break;
        
        case Formatter$Conversion.LINE_SEPARATOR: 
            if (ls == null) ls = System.getProperty("line.separator");
            Formatter.access$000(this$0).append(ls);
            break;
        
        case Formatter$Conversion.PERCENT_SIGN: 
            Formatter.access$000(this$0).append('%');
            break;
        
        default: 
            if (!$assertionsDisabled) throw new AssertionError();
        
        }
    }
    
    private void printInteger(Object arg, Locale l) throws IOException {
        if (arg == null) print("null"); else if (arg instanceof Byte) print(((Byte)(Byte)arg).byteValue(), l); else if (arg instanceof Short) print(((Short)(Short)arg).shortValue(), l); else if (arg instanceof Integer) print(((Integer)(Integer)arg).intValue(), l); else if (arg instanceof Long) print(((Long)(Long)arg).longValue(), l); else if (arg instanceof BigInteger) print(((BigInteger)(BigInteger)arg), l); else failConversion(c, arg);
    }
    
    private void printFloat(Object arg, Locale l) throws IOException {
        if (arg == null) print("null"); else if (arg instanceof Float) print(((Float)(Float)arg).floatValue(), l); else if (arg instanceof Double) print(((Double)(Double)arg).doubleValue(), l); else if (arg instanceof BigDecimal) print(((BigDecimal)(BigDecimal)arg), l); else failConversion(c, arg);
    }
    
    private void printDateTime(Object arg, Locale l) throws IOException {
        if (arg == null) {
            print("null");
            return;
        }
        Calendar cal = null;
        if (arg instanceof Long) {
            cal = Calendar.getInstance(l);
            cal.setTimeInMillis(((Long)(Long)arg).longValue());
        } else if (arg instanceof Date) {
            cal = Calendar.getInstance(l);
            cal.setTime((Date)(Date)arg);
        } else if (arg instanceof Calendar) {
            cal = (Calendar)(Calendar)((Calendar)(Calendar)arg).clone();
            cal.setLenient(true);
        } else {
            failConversion(c, arg);
        }
        print(cal, c, l);
    }
    
    private void printCharacter(Object arg) throws IOException {
        if (arg == null) {
            print("null");
            return;
        }
        String s = null;
        if (arg instanceof Character) {
            s = ((Character)(Character)arg).toString();
        } else if (arg instanceof Byte) {
            byte i = ((Byte)(Byte)arg).byteValue();
            if (Character.isValidCodePoint(i)) s = new String(Character.toChars(i)); else throw new IllegalFormatCodePointException(i);
        } else if (arg instanceof Short) {
            short i = ((Short)(Short)arg).shortValue();
            if (Character.isValidCodePoint(i)) s = new String(Character.toChars(i)); else throw new IllegalFormatCodePointException(i);
        } else if (arg instanceof Integer) {
            int i = ((Integer)(Integer)arg).intValue();
            if (Character.isValidCodePoint(i)) s = new String(Character.toChars(i)); else throw new IllegalFormatCodePointException(i);
        } else {
            failConversion(c, arg);
        }
        print(s);
    }
    
    private void printString(Object arg, Locale l) throws IOException {
        if (arg == null) {
            print("null");
        } else if (arg instanceof Formattable) {
            Formatter fmt = formatter;
            if (formatter.locale() != l) fmt = new Formatter(formatter.out(), l);
            ((Formattable)(Formattable)arg).formatTo(fmt, f.valueOf(), width, precision);
        } else {
            print(arg.toString());
        }
    }
    
    private void printBoolean(Object arg) throws IOException {
        String s;
        if (arg != null) s = ((arg instanceof Boolean) ? ((Boolean)(Boolean)arg).toString() : Boolean.toString(true)); else s = Boolean.toString(false);
        print(s);
    }
    
    private void printHashCode(Object arg) throws IOException {
        String s = (arg == null ? "null" : Integer.toHexString(arg.hashCode()));
        print(s);
    }
    
    private void print(String s) throws IOException {
        if (precision != -1 && precision < s.length()) s = s.substring(0, precision);
        if (f.contains(Formatter$Flags.UPPERCASE)) s = s.toUpperCase();
        Formatter.access$000(this$0).append(justify(s));
    }
    
    private String justify(String s) {
        if (width == -1) return s;
        StringBuilder sb = new StringBuilder();
        boolean pad = f.contains(Formatter$Flags.LEFT_JUSTIFY);
        int sp = width - s.length();
        if (!pad) for (int i = 0; i < sp; i++) sb.append(' ');
        sb.append(s);
        if (pad) for (int i = 0; i < sp; i++) sb.append(' ');
        return sb.toString();
    }
    
    public String toString() {
        StringBuilder sb = new StringBuilder('%');
        Formatter$Flags dupf = f.dup().remove(Formatter$Flags.UPPERCASE);
        sb.append(dupf.toString());
        if (index > 0) sb.append(index).append('$');
        if (width != -1) sb.append(width);
        if (precision != -1) sb.append('.').append(precision);
        if (dt) sb.append(f.contains(Formatter$Flags.UPPERCASE) ? 'T' : 't');
        sb.append(f.contains(Formatter$Flags.UPPERCASE) ? Character.toUpperCase(c) : c);
        return sb.toString();
    }
    
    private void checkGeneral() {
        if ((c == Formatter$Conversion.BOOLEAN || c == Formatter$Conversion.HASHCODE) && f.contains(Formatter$Flags.ALTERNATE)) failMismatch(Formatter$Flags.ALTERNATE, c);
        if (width == -1 && f.contains(Formatter$Flags.LEFT_JUSTIFY)) throw new MissingFormatWidthException(toString());
        checkBadFlags(new Formatter.Flags[]{Formatter$Flags.PLUS, Formatter$Flags.LEADING_SPACE, Formatter$Flags.ZERO_PAD, Formatter$Flags.GROUP, Formatter$Flags.PARENTHESES});
    }
    
    private void checkDateTime() {
        if (precision != -1) throw new IllegalFormatPrecisionException(precision);
        if (!Formatter$DateTime.isValid(c)) throw new UnknownFormatConversionException("t" + c);
        checkBadFlags(new Formatter.Flags[]{Formatter$Flags.ALTERNATE});
        if (width == -1 && f.contains(Formatter$Flags.LEFT_JUSTIFY)) throw new MissingFormatWidthException(toString());
    }
    
    private void checkCharacter() {
        if (precision != -1) throw new IllegalFormatPrecisionException(precision);
        checkBadFlags(new Formatter.Flags[]{Formatter$Flags.ALTERNATE});
        if (width == -1 && f.contains(Formatter$Flags.LEFT_JUSTIFY)) throw new MissingFormatWidthException(toString());
    }
    
    private void checkInteger() {
        checkNumeric();
        if (precision != -1) throw new IllegalFormatPrecisionException(precision);
        if (c == Formatter$Conversion.DECIMAL_INTEGER) checkBadFlags(new Formatter.Flags[]{Formatter$Flags.ALTERNATE}); else if (c == Formatter$Conversion.OCTAL_INTEGER) checkBadFlags(new Formatter.Flags[]{Formatter$Flags.GROUP}); else checkBadFlags(new Formatter.Flags[]{Formatter$Flags.GROUP});
    }
    
    private void checkBadFlags(Formatter$Flags[] badFlags) {
        for (int i = 0; i < badFlags.length; i++) if (f.contains(badFlags[i])) failMismatch(badFlags[i], c);
    }
    
    private void checkFloat() {
        checkNumeric();
        if (c == Formatter$Conversion.DECIMAL_FLOAT) {
        } else if (c == Formatter$Conversion.HEXADECIMAL_FLOAT) {
            checkBadFlags(new Formatter.Flags[]{Formatter$Flags.PARENTHESES, Formatter$Flags.GROUP});
        } else if (c == Formatter$Conversion.SCIENTIFIC) {
            checkBadFlags(new Formatter.Flags[]{Formatter$Flags.GROUP});
        } else if (c == Formatter$Conversion.GENERAL) {
            checkBadFlags(new Formatter.Flags[]{Formatter$Flags.ALTERNATE});
        }
    }
    
    private void checkNumeric() {
        if (width != -1 && width < 0) throw new IllegalFormatWidthException(width);
        if (precision != -1 && precision < 0) throw new IllegalFormatPrecisionException(precision);
        if (width == -1 && (f.contains(Formatter$Flags.LEFT_JUSTIFY) || f.contains(Formatter$Flags.ZERO_PAD))) throw new MissingFormatWidthException(toString());
        if ((f.contains(Formatter$Flags.PLUS) && f.contains(Formatter$Flags.LEADING_SPACE)) || (f.contains(Formatter$Flags.LEFT_JUSTIFY) && f.contains(Formatter$Flags.ZERO_PAD))) throw new IllegalFormatFlagsException(f.toString());
    }
    
    private void checkText() {
        if (precision != -1) throw new IllegalFormatPrecisionException(precision);
        switch (c) {
        case Formatter$Conversion.PERCENT_SIGN: 
            if (f.valueOf() != Formatter$Flags.LEFT_JUSTIFY.valueOf() && f.valueOf() != Formatter$Flags.NONE.valueOf()) throw new IllegalFormatFlagsException(f.toString());
            if (width == -1 && f.contains(Formatter$Flags.LEFT_JUSTIFY)) throw new MissingFormatWidthException(toString());
            break;
        
        case Formatter$Conversion.LINE_SEPARATOR: 
            if (width != -1) throw new IllegalFormatWidthException(width);
            if (f.valueOf() != Formatter$Flags.NONE.valueOf()) throw new IllegalFormatFlagsException(f.toString());
            break;
        
        default: 
            if (!$assertionsDisabled) throw new AssertionError();
        
        }
    }
    
    private void print(byte value, Locale l) throws IOException {
        long v = value;
        if (value < 0 && (c == Formatter$Conversion.OCTAL_INTEGER || c == Formatter$Conversion.HEXADECIMAL_INTEGER)) {
            v += (1L << 8);
            if (!$assertionsDisabled && !(v >= 0)) throw new AssertionError(v);
        }
        print(v, l);
    }
    
    private void print(short value, Locale l) throws IOException {
        long v = value;
        if (value < 0 && (c == Formatter$Conversion.OCTAL_INTEGER || c == Formatter$Conversion.HEXADECIMAL_INTEGER)) {
            v += (1L << 16);
            if (!$assertionsDisabled && !(v >= 0)) throw new AssertionError(v);
        }
        print(v, l);
    }
    
    private void print(int value, Locale l) throws IOException {
        long v = value;
        if (value < 0 && (c == Formatter$Conversion.OCTAL_INTEGER || c == Formatter$Conversion.HEXADECIMAL_INTEGER)) {
            v += (1L << 32);
            if (!$assertionsDisabled && !(v >= 0)) throw new AssertionError(v);
        }
        print(v, l);
    }
    
    private void print(long value, Locale l) throws IOException {
        StringBuilder sb = new StringBuilder();
        if (c == Formatter$Conversion.DECIMAL_INTEGER) {
            boolean neg = value < 0;
            char[] va;
            if (value < 0) va = Long.toString(value, 10).substring(1).toCharArray(); else va = Long.toString(value, 10).toCharArray();
            leadingSign(sb, neg);
            localizedMagnitude(sb, va, f, adjustWidth(width, f, neg), l);
            trailingSign(sb, neg);
        } else if (c == Formatter$Conversion.OCTAL_INTEGER) {
            checkBadFlags(new Formatter.Flags[]{Formatter$Flags.PARENTHESES, Formatter$Flags.LEADING_SPACE, Formatter$Flags.PLUS});
            String s = Long.toOctalString(value);
            int len = (f.contains(Formatter$Flags.ALTERNATE) ? s.length() + 1 : s.length());
            if (f.contains(Formatter$Flags.ALTERNATE)) sb.append('0');
            if (f.contains(Formatter$Flags.ZERO_PAD)) for (int i = 0; i < width - len; i++) sb.append('0');
            sb.append(s);
        } else if (c == Formatter$Conversion.HEXADECIMAL_INTEGER) {
            checkBadFlags(new Formatter.Flags[]{Formatter$Flags.PARENTHESES, Formatter$Flags.LEADING_SPACE, Formatter$Flags.PLUS});
            String s = Long.toHexString(value);
            int len = (f.contains(Formatter$Flags.ALTERNATE) ? s.length() + 2 : s.length());
            if (f.contains(Formatter$Flags.ALTERNATE)) sb.append(f.contains(Formatter$Flags.UPPERCASE) ? "0X" : "0x");
            if (f.contains(Formatter$Flags.ZERO_PAD)) for (int i = 0; i < width - len; i++) sb.append('0');
            if (f.contains(Formatter$Flags.UPPERCASE)) s = s.toUpperCase();
            sb.append(s);
        }
        Formatter.access$000(this$0).append(justify(sb.toString()));
    }
    
    private StringBuilder leadingSign(StringBuilder sb, boolean neg) {
        if (!neg) {
            if (f.contains(Formatter$Flags.PLUS)) {
                sb.append('+');
            } else if (f.contains(Formatter$Flags.LEADING_SPACE)) {
                sb.append(' ');
            }
        } else {
            if (f.contains(Formatter$Flags.PARENTHESES)) sb.append('('); else sb.append('-');
        }
        return sb;
    }
    
    private StringBuilder trailingSign(StringBuilder sb, boolean neg) {
        if (neg && f.contains(Formatter$Flags.PARENTHESES)) sb.append(')');
        return sb;
    }
    
    private void print(BigInteger value, Locale l) throws IOException {
        StringBuilder sb = new StringBuilder();
        boolean neg = value.signum() == -1;
        BigInteger v = value.abs();
        leadingSign(sb, neg);
        if (c == Formatter$Conversion.DECIMAL_INTEGER) {
            char[] va = v.toString().toCharArray();
            localizedMagnitude(sb, va, f, adjustWidth(width, f, neg), l);
        } else if (c == Formatter$Conversion.OCTAL_INTEGER) {
            String s = v.toString(8);
            int len = s.length() + sb.length();
            if (neg && f.contains(Formatter$Flags.PARENTHESES)) len++;
            if (f.contains(Formatter$Flags.ALTERNATE)) {
                len++;
                sb.append('0');
            }
            if (f.contains(Formatter$Flags.ZERO_PAD)) {
                for (int i = 0; i < width - len; i++) sb.append('0');
            }
            sb.append(s);
        } else if (c == Formatter$Conversion.HEXADECIMAL_INTEGER) {
            String s = v.toString(16);
            int len = s.length() + sb.length();
            if (neg && f.contains(Formatter$Flags.PARENTHESES)) len++;
            if (f.contains(Formatter$Flags.ALTERNATE)) {
                len += 2;
                sb.append(f.contains(Formatter$Flags.UPPERCASE) ? "0X" : "0x");
            }
            if (f.contains(Formatter$Flags.ZERO_PAD)) for (int i = 0; i < width - len; i++) sb.append('0');
            if (f.contains(Formatter$Flags.UPPERCASE)) s = s.toUpperCase();
            sb.append(s);
        }
        trailingSign(sb, (value.signum() == -1));
        Formatter.access$000(this$0).append(justify(sb.toString()));
    }
    
    private void print(float value, Locale l) throws IOException {
        print((double)value, l);
    }
    
    private void print(double value, Locale l) throws IOException {
        StringBuilder sb = new StringBuilder();
        boolean neg = Double.compare(value, 0.0) == -1;
        if (!Double.isNaN(value)) {
            double v = Math.abs(value);
            leadingSign(sb, neg);
            if (!Double.isInfinite(v)) print(sb, v, l, f, c, precision, neg); else sb.append(f.contains(Formatter$Flags.UPPERCASE) ? "INFINITY" : "Infinity");
            trailingSign(sb, neg);
        } else {
            sb.append(f.contains(Formatter$Flags.UPPERCASE) ? "NAN" : "NaN");
        }
        Formatter.access$000(this$0).append(justify(sb.toString()));
    }
    
    private void print(StringBuilder sb, double value, Locale l, Formatter$Flags f, char c, int precision, boolean neg) throws IOException {
        if (c == Formatter$Conversion.SCIENTIFIC) {
            int prec = (precision == -1 ? 6 : precision);
            FormattedFloatingDecimal fd = new FormattedFloatingDecimal(value, prec, FormattedFloatingDecimal$Form.SCIENTIFIC);
            char[] v = new char[30];
            int len = fd.getChars(v);
            char[] mant = addZeros(mantissa(v, len), prec);
            if (f.contains(Formatter$Flags.ALTERNATE) && (prec == 0)) mant = addDot(mant);
            char[] exp = (value == 0.0) ? new char[]{'+', '0', '0'} : exponent(v, len);
            int newW = width;
            if (width != -1) newW = adjustWidth(width - exp.length - 1, f, neg);
            localizedMagnitude(sb, mant, f, newW, null);
            sb.append(f.contains(Formatter$Flags.UPPERCASE) ? 'E' : 'e');
            Formatter$Flags flags = f.dup().remove(Formatter$Flags.GROUP);
            char sign = exp[0];
            if (!$assertionsDisabled && !(sign == '+' || sign == '-')) throw new AssertionError();
            sb.append(sign);
            char[] tmp = new char[exp.length - 1];
            System.arraycopy(exp, 1, tmp, 0, exp.length - 1);
            sb.append(localizedMagnitude(null, tmp, flags, -1, null));
        } else if (c == Formatter$Conversion.DECIMAL_FLOAT) {
            int prec = (precision == -1 ? 6 : precision);
            FormattedFloatingDecimal fd = new FormattedFloatingDecimal(value, prec, FormattedFloatingDecimal$Form.DECIMAL_FLOAT);
            char[] v = new char[30 + 1 + Math.abs(fd.getExponent())];
            int len = fd.getChars(v);
            char[] mant = addZeros(mantissa(v, len), prec);
            if (f.contains(Formatter$Flags.ALTERNATE) && (prec == 0)) mant = addDot(mant);
            int newW = width;
            if (width != -1) newW = adjustWidth(width, f, neg);
            localizedMagnitude(sb, mant, f, newW, l);
        } else if (c == Formatter$Conversion.GENERAL) {
            int prec = precision;
            if (precision == -1) prec = 6; else if (precision == 0) prec = 1;
            FormattedFloatingDecimal fd = new FormattedFloatingDecimal(value, prec, FormattedFloatingDecimal$Form.GENERAL);
            char[] v = new char[30 + 1 + Math.abs(fd.getExponent())];
            int len = fd.getChars(v);
            char[] exp = exponent(v, len);
            if (exp != null) {
                prec -= 1;
            } else {
                prec = prec - (value == 0 ? 0 : fd.getExponentRounded()) - 1;
            }
            char[] mant = addZeros(mantissa(v, len), prec);
            if (f.contains(Formatter$Flags.ALTERNATE) && (prec == 0)) mant = addDot(mant);
            int newW = width;
            if (width != -1) {
                if (exp != null) newW = adjustWidth(width - exp.length - 1, f, neg); else newW = adjustWidth(width, f, neg);
            }
            localizedMagnitude(sb, mant, f, newW, null);
            if (exp != null) {
                sb.append(f.contains(Formatter$Flags.UPPERCASE) ? 'E' : 'e');
                Formatter$Flags flags = f.dup().remove(Formatter$Flags.GROUP);
                char sign = exp[0];
                if (!$assertionsDisabled && !(sign == '+' || sign == '-')) throw new AssertionError();
                sb.append(sign);
                char[] tmp = new char[exp.length - 1];
                System.arraycopy(exp, 1, tmp, 0, exp.length - 1);
                sb.append(localizedMagnitude(null, tmp, flags, -1, null));
            }
        } else if (c == Formatter$Conversion.HEXADECIMAL_FLOAT) {
            int prec = precision;
            if (precision == -1) prec = 0; else if (precision == 0) prec = 1;
            String s = hexDouble(value, prec);
            char[] va;
            boolean upper = f.contains(Formatter$Flags.UPPERCASE);
            sb.append(upper ? "0X" : "0x");
            if (f.contains(Formatter$Flags.ZERO_PAD)) for (int i = 0; i < width - s.length() - 2; i++) sb.append('0');
            int idx = s.indexOf('p');
            va = s.substring(0, idx).toCharArray();
            if (upper) {
                String tmp = new String(va);
                tmp = tmp.toUpperCase(Locale.US);
                va = tmp.toCharArray();
            }
            sb.append(prec != 0 ? addZeros(va, prec) : va);
            sb.append(upper ? 'P' : 'p');
            sb.append(s.substring(idx + 1));
        }
    }
    
    private char[] mantissa(char[] v, int len) {
        int i;
        for (i = 0; i < len; i++) {
            if (v[i] == 'e') break;
        }
        char[] tmp = new char[i];
        System.arraycopy(v, 0, tmp, 0, i);
        return tmp;
    }
    
    private char[] exponent(char[] v, int len) {
        int i;
        for (i = len - 1; i >= 0; i--) {
            if (v[i] == 'e') break;
        }
        if (i == -1) return null;
        char[] tmp = new char[len - i - 1];
        System.arraycopy(v, i + 1, tmp, 0, len - i - 1);
        return tmp;
    }
    
    private char[] addZeros(char[] v, int prec) {
        int i;
        for (i = 0; i < v.length; i++) {
            if (v[i] == '.') break;
        }
        boolean needDot = false;
        if (i == v.length) {
            needDot = true;
        }
        int outPrec = v.length - i - (needDot ? 0 : 1);
        if (!$assertionsDisabled && !(outPrec <= prec)) throw new AssertionError();
        if (outPrec == prec) return v;
        char[] tmp = new char[v.length + prec - outPrec + (needDot ? 1 : 0)];
        System.arraycopy(v, 0, tmp, 0, v.length);
        int start = v.length;
        if (needDot) {
            tmp[v.length] = '.';
            start++;
        }
        for (int j = start; j < tmp.length; j++) tmp[j] = '0';
        return tmp;
    }
    
    private String hexDouble(double d, int prec) {
        if (!FpUtils.isFinite(d) || d == 0.0 || prec == 0 || prec >= 13) return Double.toHexString(d).substring(2); else {
            if (!$assertionsDisabled && !(prec >= 1 && prec <= 12)) throw new AssertionError();
            int exponent = FpUtils.getExponent(d);
            boolean subnormal = (exponent == DoubleConsts.MIN_EXPONENT - 1);
            if (subnormal) {
                Formatter.access$202(FpUtils.scalb(1.0, 54));
                d *= Formatter.access$200();
                exponent = FpUtils.getExponent(d);
                if (!$assertionsDisabled && !(exponent >= DoubleConsts.MIN_EXPONENT && exponent <= DoubleConsts.MAX_EXPONENT)) throw new AssertionError(exponent);
            }
            int precision = 1 + prec * 4;
            int shiftDistance = DoubleConsts.SIGNIFICAND_WIDTH - precision;
            if (!$assertionsDisabled && !(shiftDistance >= 1 && shiftDistance < DoubleConsts.SIGNIFICAND_WIDTH)) throw new AssertionError();
            long doppel = Double.doubleToLongBits(d);
            long newSignif = (doppel & (DoubleConsts.EXP_BIT_MASK | DoubleConsts.SIGNIF_BIT_MASK)) >> shiftDistance;
            long roundingBits = doppel & ~(~0L << shiftDistance);
            boolean leastZero = (newSignif & 1L) == 0L;
            boolean round = ((1L << (shiftDistance - 1)) & roundingBits) != 0L;
            boolean sticky = shiftDistance > 1 && (~(1L << (shiftDistance - 1)) & roundingBits) != 0;
            if ((leastZero && round && sticky) || (!leastZero && round)) {
                newSignif++;
            }
            long signBit = doppel & DoubleConsts.SIGN_BIT_MASK;
            newSignif = signBit | (newSignif << shiftDistance);
            double result = Double.longBitsToDouble(newSignif);
            if (Double.isInfinite(result)) {
                return "1.0p1024";
            } else {
                String res = Double.toHexString(result).substring(2);
                if (!subnormal) return res; else {
                    int idx = res.indexOf('p');
                    if (idx == -1) {
                        if (!$assertionsDisabled) throw new AssertionError();
                        return null;
                    } else {
                        String exp = res.substring(idx + 1);
                        int iexp = Integer.parseInt(exp) - 54;
                        return res.substring(0, idx) + "p" + Integer.toString(iexp);
                    }
                }
            }
        }
    }
    
    private void print(BigDecimal value, Locale l) throws IOException {
        if (c == Formatter$Conversion.HEXADECIMAL_FLOAT) failConversion(c, value);
        StringBuilder sb = new StringBuilder();
        boolean neg = value.signum() == -1;
        BigDecimal v = value.abs();
        leadingSign(sb, neg);
        print(sb, v, l, f, c, precision, neg);
        trailingSign(sb, neg);
        Formatter.access$000(this$0).append(justify(sb.toString()));
    }
    
    private void print(StringBuilder sb, BigDecimal value, Locale l, Formatter$Flags f, char c, int precision, boolean neg) throws IOException {
        if (c == Formatter$Conversion.SCIENTIFIC) {
            int prec = (precision == -1 ? 6 : precision);
            int scale = value.scale();
            int origPrec = value.precision();
            int nzeros = 0;
            int compPrec;
            if (prec > origPrec - 1) {
                compPrec = origPrec;
                nzeros = prec - (origPrec - 1);
            } else {
                compPrec = prec + 1;
            }
            MathContext mc = new MathContext(compPrec);
            BigDecimal v = new BigDecimal(value.unscaledValue(), scale, mc);
            Formatter$FormatSpecifier$BigDecimalLayout bdl = new Formatter$FormatSpecifier$BigDecimalLayout(this, v.unscaledValue(), v.scale(), Formatter$BigDecimalLayoutForm.SCIENTIFIC);
            char[] mant = bdl.mantissa();
            if ((origPrec == 1 || !bdl.hasDot()) && (nzeros > 0 || (f.contains(Formatter$Flags.ALTERNATE)))) mant = addDot(mant);
            mant = trailingZeros(mant, nzeros);
            char[] exp = bdl.exponent();
            int newW = width;
            if (width != -1) newW = adjustWidth(width - exp.length - 1, f, neg);
            localizedMagnitude(sb, mant, f, newW, null);
            sb.append(f.contains(Formatter$Flags.UPPERCASE) ? 'E' : 'e');
            Formatter$Flags flags = f.dup().remove(Formatter$Flags.GROUP);
            char sign = exp[0];
            if (!$assertionsDisabled && !(sign == '+' || sign == '-')) throw new AssertionError();
            sb.append(exp[0]);
            char[] tmp = new char[exp.length - 1];
            System.arraycopy(exp, 1, tmp, 0, exp.length - 1);
            sb.append(localizedMagnitude(null, tmp, flags, -1, null));
        } else if (c == Formatter$Conversion.DECIMAL_FLOAT) {
            int prec = (precision == -1 ? 6 : precision);
            int scale = value.scale();
            int origPrec = value.precision();
            int nzeros = 0;
            int compPrec;
            if (scale < prec) {
                compPrec = origPrec;
                nzeros = prec - scale;
            } else {
                compPrec = origPrec - (scale - prec);
            }
            MathContext mc = new MathContext(compPrec);
            BigDecimal v = new BigDecimal(value.unscaledValue(), scale, mc);
            Formatter$FormatSpecifier$BigDecimalLayout bdl = new Formatter$FormatSpecifier$BigDecimalLayout(this, v.unscaledValue(), v.scale(), Formatter$BigDecimalLayoutForm.DECIMAL_FLOAT);
            char[] mant = bdl.mantissa();
            if (scale == 0 && (f.contains(Formatter$Flags.ALTERNATE) || nzeros > 0)) mant = addDot(bdl.mantissa());
            mant = trailingZeros(mant, nzeros);
            localizedMagnitude(sb, mant, f, adjustWidth(width, f, neg), l);
        } else if (c == Formatter$Conversion.GENERAL) {
            int prec = precision;
            if (precision == -1) prec = 6; else if (precision == 0) prec = 1;
            BigDecimal tenToTheNegFour = BigDecimal.valueOf(1, 4);
            BigDecimal tenToThePrec = BigDecimal.valueOf(1, -prec);
            if ((value.equals(BigDecimal.ZERO)) || ((value.compareTo(tenToTheNegFour) != -1) && (value.compareTo(tenToThePrec) == -1))) {
                int e = -value.scale() + (value.unscaledValue().toString().length() - 1);
                prec = prec - e - 1;
                print(sb, value, l, f, Formatter$Conversion.DECIMAL_FLOAT, prec, neg);
            } else {
                print(sb, value, l, f, Formatter$Conversion.SCIENTIFIC, prec - 1, neg);
            }
        } else if (c == Formatter$Conversion.HEXADECIMAL_FLOAT) {
            if (!$assertionsDisabled) throw new AssertionError();
        }
    }
    {
    }
    
    private int adjustWidth(int width, Formatter$Flags f, boolean neg) {
        int newW = width;
        if (newW != -1 && neg && f.contains(Formatter$Flags.PARENTHESES)) newW--;
        return newW;
    }
    
    private char[] addDot(char[] mant) {
        char[] tmp = mant;
        tmp = new char[mant.length + 1];
        System.arraycopy(mant, 0, tmp, 0, mant.length);
        tmp[tmp.length - 1] = '.';
        return tmp;
    }
    
    private char[] trailingZeros(char[] mant, int nzeros) {
        char[] tmp = mant;
        if (nzeros > 0) {
            tmp = new char[mant.length + nzeros];
            System.arraycopy(mant, 0, tmp, 0, mant.length);
            for (int i = mant.length; i < tmp.length; i++) tmp[i] = '0';
        }
        return tmp;
    }
    
    private void print(Calendar t, char c, Locale l) throws IOException {
        StringBuilder sb = new StringBuilder();
        print(sb, t, c, l);
        String s = justify(sb.toString());
        if (f.contains(Formatter$Flags.UPPERCASE)) s = s.toUpperCase();
        Formatter.access$000(this$0).append(s);
    }
    
    private Appendable print(StringBuilder sb, Calendar t, char c, Locale l) throws IOException {
        if (!$assertionsDisabled && !(width == -1)) throw new AssertionError();
        if (sb == null) sb = new StringBuilder();
        switch (c) {
        case Formatter$DateTime.HOUR_OF_DAY_0: 
        
        case Formatter$DateTime.HOUR_0: 
        
        case Formatter$DateTime.HOUR_OF_DAY: 
        
        case Formatter$DateTime.HOUR: 
            {
                int i = t.get(Calendar.HOUR_OF_DAY);
                if (c == Formatter$DateTime.HOUR_0 || c == Formatter$DateTime.HOUR) i = (i == 0 || i == 12 ? 12 : i % 12);
                Formatter$Flags flags = (c == Formatter$DateTime.HOUR_OF_DAY_0 || c == Formatter$DateTime.HOUR_0 ? Formatter$Flags.ZERO_PAD : Formatter$Flags.NONE);
                sb.append(localizedMagnitude(null, i, flags, 2, l));
                break;
            }
        
        case Formatter$DateTime.MINUTE: 
            {
                int i = t.get(Calendar.MINUTE);
                Formatter$Flags flags = Formatter$Flags.ZERO_PAD;
                sb.append(localizedMagnitude(null, i, flags, 2, l));
                break;
            }
        
        case Formatter$DateTime.NANOSECOND: 
            {
                int i = t.get(Calendar.MILLISECOND) * 1000000;
                Formatter$Flags flags = Formatter$Flags.ZERO_PAD;
                sb.append(localizedMagnitude(null, i, flags, 9, l));
                break;
            }
        
        case Formatter$DateTime.MILLISECOND: 
            {
                int i = t.get(Calendar.MILLISECOND);
                Formatter$Flags flags = Formatter$Flags.ZERO_PAD;
                sb.append(localizedMagnitude(null, i, flags, 3, l));
                break;
            }
        
        case Formatter$DateTime.MILLISECOND_SINCE_EPOCH: 
            {
                long i = t.getTimeInMillis();
                Formatter$Flags flags = Formatter$Flags.NONE;
                sb.append(localizedMagnitude(null, i, flags, width, l));
                break;
            }
        
        case Formatter$DateTime.AM_PM: 
            {
                String[] ampm = {"AM", "PM"};
                if (l != null && l != Locale.US) {
                    DateFormatSymbols dfs = new DateFormatSymbols(l);
                    ampm = dfs.getAmPmStrings();
                }
                String s = ampm[t.get(Calendar.AM_PM)];
                sb.append(s.toLowerCase(l != null ? l : Locale.US));
                break;
            }
        
        case Formatter$DateTime.SECONDS_SINCE_EPOCH: 
            {
                long i = t.getTimeInMillis() / 1000;
                Formatter$Flags flags = Formatter$Flags.NONE;
                sb.append(localizedMagnitude(null, i, flags, width, l));
                break;
            }
        
        case Formatter$DateTime.SECOND: 
            {
                int i = t.get(Calendar.SECOND);
                Formatter$Flags flags = Formatter$Flags.ZERO_PAD;
                sb.append(localizedMagnitude(null, i, flags, 2, l));
                break;
            }
        
        case Formatter$DateTime.ZONE_NUMERIC: 
            {
                int i = t.get(Calendar.ZONE_OFFSET);
                boolean neg = i < 0;
                sb.append(neg ? '-' : '+');
                if (neg) i = -i;
                int min = i / 60000;
                int offset = (min / 60) * 100 + (min % 60);
                Formatter$Flags flags = Formatter$Flags.ZERO_PAD;
                sb.append(localizedMagnitude(null, offset, flags, 4, l));
                break;
            }
        
        case Formatter$DateTime.ZONE: 
            {
                TimeZone tz = t.getTimeZone();
                sb.append(tz.getDisplayName((t.get(Calendar.DST_OFFSET) != 0), TimeZone.SHORT, l));
                break;
            }
        
        case Formatter$DateTime.NAME_OF_DAY_ABBREV: 
        
        case Formatter$DateTime.NAME_OF_DAY: 
            {
                int i = t.get(Calendar.DAY_OF_WEEK);
                Locale lt = ((l == null) ? Locale.US : l);
                DateFormatSymbols dfs = new DateFormatSymbols(lt);
                if (c == Formatter$DateTime.NAME_OF_DAY) sb.append(dfs.getWeekdays()[i]); else sb.append(dfs.getShortWeekdays()[i]);
                break;
            }
        
        case Formatter$DateTime.NAME_OF_MONTH_ABBREV: 
        
        case Formatter$DateTime.NAME_OF_MONTH_ABBREV_X: 
        
        case Formatter$DateTime.NAME_OF_MONTH: 
            {
                int i = t.get(Calendar.MONTH);
                Locale lt = ((l == null) ? Locale.US : l);
                DateFormatSymbols dfs = new DateFormatSymbols(lt);
                if (c == Formatter$DateTime.NAME_OF_MONTH) sb.append(dfs.getMonths()[i]); else sb.append(dfs.getShortMonths()[i]);
                break;
            }
        
        case Formatter$DateTime.CENTURY: 
        
        case Formatter$DateTime.YEAR_2: 
        
        case Formatter$DateTime.YEAR_4: 
            {
                int i = t.get(Calendar.YEAR);
                int size = 2;
                switch (c) {
                case Formatter$DateTime.CENTURY: 
                    i /= 100;
                    break;
                
                case Formatter$DateTime.YEAR_2: 
                    i %= 100;
                    break;
                
                case Formatter$DateTime.YEAR_4: 
                    size = 4;
                    break;
                
                }
                Formatter$Flags flags = Formatter$Flags.ZERO_PAD;
                sb.append(localizedMagnitude(null, i, flags, size, l));
                break;
            }
        
        case Formatter$DateTime.DAY_OF_MONTH_0: 
        
        case Formatter$DateTime.DAY_OF_MONTH: 
            {
                int i = t.get(Calendar.DATE);
                Formatter$Flags flags = (c == Formatter$DateTime.DAY_OF_MONTH_0 ? Formatter$Flags.ZERO_PAD : Formatter$Flags.NONE);
                sb.append(localizedMagnitude(null, i, flags, 2, l));
                break;
            }
        
        case Formatter$DateTime.DAY_OF_YEAR: 
            {
                int i = t.get(Calendar.DAY_OF_YEAR);
                Formatter$Flags flags = Formatter$Flags.ZERO_PAD;
                sb.append(localizedMagnitude(null, i, flags, 3, l));
                break;
            }
        
        case Formatter$DateTime.MONTH: 
            {
                int i = t.get(Calendar.MONTH) + 1;
                Formatter$Flags flags = Formatter$Flags.ZERO_PAD;
                sb.append(localizedMagnitude(null, i, flags, 2, l));
                break;
            }
        
        case Formatter$DateTime.TIME: 
        
        case Formatter$DateTime.TIME_24_HOUR: 
            {
                char sep = ':';
                print(sb, t, Formatter$DateTime.HOUR_OF_DAY_0, l).append(sep);
                print(sb, t, Formatter$DateTime.MINUTE, l);
                if (c == Formatter$DateTime.TIME) {
                    sb.append(sep);
                    print(sb, t, Formatter$DateTime.SECOND, l);
                }
                break;
            }
        
        case Formatter$DateTime.TIME_12_HOUR: 
            {
                char sep = ':';
                print(sb, t, Formatter$DateTime.HOUR_0, l).append(sep);
                print(sb, t, Formatter$DateTime.MINUTE, l).append(sep);
                print(sb, t, Formatter$DateTime.SECOND, l).append(' ');
                StringBuilder tsb = new StringBuilder();
                print(tsb, t, Formatter$DateTime.AM_PM, l);
                sb.append(tsb.toString().toUpperCase(l != null ? l : Locale.US));
                break;
            }
        
        case Formatter$DateTime.DATE_TIME: 
            {
                char sep = ' ';
                print(sb, t, Formatter$DateTime.NAME_OF_DAY_ABBREV, l).append(sep);
                print(sb, t, Formatter$DateTime.NAME_OF_MONTH_ABBREV, l).append(sep);
                print(sb, t, Formatter$DateTime.DAY_OF_MONTH_0, l).append(sep);
                print(sb, t, Formatter$DateTime.TIME, l).append(sep);
                print(sb, t, Formatter$DateTime.ZONE, l).append(sep);
                print(sb, t, Formatter$DateTime.YEAR_4, l);
                break;
            }
        
        case Formatter$DateTime.DATE: 
            {
                char sep = '/';
                print(sb, t, Formatter$DateTime.MONTH, l).append(sep);
                print(sb, t, Formatter$DateTime.DAY_OF_MONTH_0, l).append(sep);
                print(sb, t, Formatter$DateTime.YEAR_2, l);
                break;
            }
        
        case Formatter$DateTime.ISO_STANDARD_DATE: 
            {
                char sep = '-';
                print(sb, t, Formatter$DateTime.YEAR_4, l).append(sep);
                print(sb, t, Formatter$DateTime.MONTH, l).append(sep);
                print(sb, t, Formatter$DateTime.DAY_OF_MONTH_0, l);
                break;
            }
        
        default: 
            if (!$assertionsDisabled) throw new AssertionError();
        
        }
        return sb;
    }
    
    private void failMismatch(Formatter$Flags f, char c) {
        String fs = f.toString();
        throw new FormatFlagsConversionMismatchException(fs, c);
    }
    
    private void failConversion(char c, Object arg) {
        throw new IllegalFormatConversionException(c, arg.getClass());
    }
    
    private char getZero(Locale l) {
        if ((l != null) && !l.equals(this$0.locale())) {
            DecimalFormatSymbols dfs = new DecimalFormatSymbols(l);
            return dfs.getZeroDigit();
        }
        return Formatter.access$300(this$0);
    }
    
    private StringBuilder localizedMagnitude(StringBuilder sb, long value, Formatter$Flags f, int width, Locale l) {
        char[] va = Long.toString(value, 10).toCharArray();
        return localizedMagnitude(sb, va, f, width, l);
    }
    
    private StringBuilder localizedMagnitude(StringBuilder sb, char[] value, Formatter$Flags f, int width, Locale l) {
        if (sb == null) sb = new StringBuilder();
        int begin = sb.length();
        char zero = getZero(l);
        char grpSep = '\000';
        int grpSize = -1;
        char decSep = '\000';
        int len = value.length;
        int dot = len;
        for (int j = 0; j < len; j++) {
            if (value[j] == '.') {
                dot = j;
                break;
            }
        }
        if (dot < len) {
            if (l == null || l.equals(Locale.US)) {
                decSep = '.';
            } else {
                DecimalFormatSymbols dfs = new DecimalFormatSymbols(l);
                decSep = dfs.getDecimalSeparator();
            }
        }
        if (f.contains(Formatter$Flags.GROUP)) {
            if (l == null || l.equals(Locale.US)) {
                grpSep = ',';
                grpSize = 3;
            } else {
                DecimalFormatSymbols dfs = new DecimalFormatSymbols(l);
                grpSep = dfs.getGroupingSeparator();
                DecimalFormat df = (DecimalFormat)(DecimalFormat)NumberFormat.getIntegerInstance(l);
                grpSize = df.getGroupingSize();
            }
        }
        for (int j = 0; j < len; j++) {
            if (j == dot) {
                sb.append(decSep);
                grpSep = '\000';
                continue;
            }
            char c = value[j];
            sb.append((char)((c - '0') + zero));
            if (grpSep != '\000' && j != dot - 1 && ((dot - j) % grpSize == 1)) sb.append(grpSep);
        }
        len = sb.length();
        if (width != -1 && f.contains(Formatter$Flags.ZERO_PAD)) for (int k = 0; k < width - len; k++) sb.insert(begin, zero);
        return sb;
    }
}
