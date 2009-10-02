package java.text;

import java.io.InvalidObjectException;
import java.io.IOException;
import java.io.ObjectInputStream;
import sun.text.Utility;

public class ChoiceFormat extends NumberFormat {
    private static final long serialVersionUID = 1795184449645032964L;
    
    public void applyPattern(String newPattern) {
        StringBuffer[] segments = new StringBuffer[2];
        for (int i = 0; i < segments.length; ++i) {
            segments[i] = new StringBuffer();
        }
        double[] newChoiceLimits = new double[30];
        String[] newChoiceFormats = new String[30];
        int count = 0;
        int part = 0;
        double startValue = 0;
        double oldStartValue = Double.NaN;
        boolean inQuote = false;
        for (int i = 0; i < newPattern.length(); ++i) {
            char ch = newPattern.charAt(i);
            if (ch == '\'') {
                if ((i + 1) < newPattern.length() && newPattern.charAt(i + 1) == ch) {
                    segments[part].append(ch);
                    ++i;
                } else {
                    inQuote = !inQuote;
                }
            } else if (inQuote) {
                segments[part].append(ch);
            } else if (ch == '<' || ch == '#' || ch == '\u2264') {
                if (segments[0].equals("")) {
                    throw new IllegalArgumentException();
                }
                try {
                    String tempBuffer = segments[0].toString();
                    if (tempBuffer.equals("\u221e")) {
                        startValue = Double.POSITIVE_INFINITY;
                    } else if (tempBuffer.equals("-\u221e")) {
                        startValue = Double.NEGATIVE_INFINITY;
                    } else {
                        startValue = Double.valueOf(segments[0].toString()).doubleValue();
                    }
                } catch (Exception e) {
                    throw new IllegalArgumentException();
                }
                if (ch == '<' && startValue != Double.POSITIVE_INFINITY && startValue != Double.NEGATIVE_INFINITY) {
                    startValue = nextDouble(startValue);
                }
                if (startValue <= oldStartValue) {
                    throw new IllegalArgumentException();
                }
                segments[0].setLength(0);
                part = 1;
            } else if (ch == '|') {
                if (count == newChoiceLimits.length) {
                    newChoiceLimits = doubleArraySize(newChoiceLimits);
                    newChoiceFormats = doubleArraySize(newChoiceFormats);
                }
                newChoiceLimits[count] = startValue;
                newChoiceFormats[count] = segments[1].toString();
                ++count;
                oldStartValue = startValue;
                segments[1].setLength(0);
                part = 0;
            } else {
                segments[part].append(ch);
            }
        }
        if (part == 1) {
            if (count == newChoiceLimits.length) {
                newChoiceLimits = doubleArraySize(newChoiceLimits);
                newChoiceFormats = doubleArraySize(newChoiceFormats);
            }
            newChoiceLimits[count] = startValue;
            newChoiceFormats[count] = segments[1].toString();
            ++count;
        }
        choiceLimits = new double[count];
        System.arraycopy(newChoiceLimits, 0, choiceLimits, 0, count);
        choiceFormats = new String[count];
        System.arraycopy(newChoiceFormats, 0, choiceFormats, 0, count);
    }
    
    public String toPattern() {
        StringBuffer result = new StringBuffer();
        for (int i = 0; i < choiceLimits.length; ++i) {
            if (i != 0) {
                result.append('|');
            }
            double less = previousDouble(choiceLimits[i]);
            double tryLessOrEqual = Math.abs(Math.IEEEremainder(choiceLimits[i], 1.0));
            double tryLess = Math.abs(Math.IEEEremainder(less, 1.0));
            if (tryLessOrEqual < tryLess) {
                result.append("" + choiceLimits[i]);
                result.append('#');
            } else {
                if (choiceLimits[i] == Double.POSITIVE_INFINITY) {
                    result.append("\u221e");
                } else if (choiceLimits[i] == Double.NEGATIVE_INFINITY) {
                    result.append("-\u221e");
                } else {
                    result.append("" + less);
                }
                result.append('<');
            }
            String text = choiceFormats[i];
            boolean needQuote = text.indexOf('<') >= 0 || text.indexOf('#') >= 0 || text.indexOf('\u2264') >= 0 || text.indexOf('|') >= 0;
            if (needQuote) result.append('\'');
            if (text.indexOf('\'') < 0) result.append(text); else {
                for (int j = 0; j < text.length(); ++j) {
                    char c = text.charAt(j);
                    result.append(c);
                    if (c == '\'') result.append(c);
                }
            }
            if (needQuote) result.append('\'');
        }
        return result.toString();
    }
    
    public ChoiceFormat(String newPattern) {
        
        applyPattern(newPattern);
    }
    
    public ChoiceFormat(double[] limits, String[] formats) {
        
        setChoices(limits, formats);
    }
    
    public void setChoices(double[] limits, String[] formats) {
        if (limits.length != formats.length) {
            throw new IllegalArgumentException("Array and limit arrays must be of the same length.");
        }
        choiceLimits = limits;
        choiceFormats = formats;
    }
    
    public double[] getLimits() {
        return choiceLimits;
    }
    
    public Object[] getFormats() {
        return choiceFormats;
    }
    
    public StringBuffer format(long number, StringBuffer toAppendTo, FieldPosition status) {
        return format((double)number, toAppendTo, status);
    }
    
    public StringBuffer format(double number, StringBuffer toAppendTo, FieldPosition status) {
        int i;
        for (i = 0; i < choiceLimits.length; ++i) {
            if (!(number >= choiceLimits[i])) {
                break;
            }
        }
        --i;
        if (i < 0) i = 0;
        return toAppendTo.append(choiceFormats[i]);
    }
    
    public Number parse(String text, ParsePosition status) {
        int start = status.index;
        int furthest = start;
        double bestNumber = Double.NaN;
        double tempNumber = 0.0;
        for (int i = 0; i < choiceFormats.length; ++i) {
            String tempString = choiceFormats[i];
            if (text.regionMatches(start, tempString, 0, tempString.length())) {
                status.index = start + tempString.length();
                tempNumber = choiceLimits[i];
                if (status.index > furthest) {
                    furthest = status.index;
                    bestNumber = tempNumber;
                    if (furthest == text.length()) break;
                }
            }
        }
        status.index = furthest;
        if (status.index == start) {
            status.errorIndex = furthest;
        }
        return new Double(bestNumber);
    }
    
    public static final double nextDouble(double d) {
        return nextDouble(d, true);
    }
    
    public static final double previousDouble(double d) {
        return nextDouble(d, false);
    }
    
    public Object clone() {
        ChoiceFormat other = (ChoiceFormat)(ChoiceFormat)super.clone();
        other.choiceLimits = (double[])(double[])choiceLimits.clone();
        other.choiceFormats = (String[])(String[])choiceFormats.clone();
        return other;
    }
    
    public int hashCode() {
        int result = choiceLimits.length;
        if (choiceFormats.length > 0) {
            result ^= choiceFormats[choiceFormats.length - 1].hashCode();
        }
        return result;
    }
    
    public boolean equals(Object obj) {
        if (obj == null) return false;
        if (this == obj) return true;
        if (getClass() != obj.getClass()) return false;
        ChoiceFormat other = (ChoiceFormat)(ChoiceFormat)obj;
        return (Utility.arrayEquals(choiceLimits, other.choiceLimits) && Utility.arrayEquals(choiceFormats, other.choiceFormats));
    }
    
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        if (choiceLimits.length != choiceFormats.length) {
            throw new InvalidObjectException("limits and format arrays of different length.");
        }
    }
    private double[] choiceLimits;
    private String[] choiceFormats;
    static final long SIGN = -9223372036854775808L;
    static final long EXPONENT = 9218868437227405312L;
    static final long POSITIVEINFINITY = 9218868437227405312L;
    
    public static double nextDouble(double d, boolean positive) {
        if (Double.isNaN(d)) {
            return d;
        }
        if (d == 0.0) {
            double smallestPositiveDouble = Double.longBitsToDouble(1L);
            if (positive) {
                return smallestPositiveDouble;
            } else {
                return -smallestPositiveDouble;
            }
        }
        long bits = Double.doubleToLongBits(d);
        long magnitude = bits & ~SIGN;
        if ((bits > 0) == positive) {
            if (magnitude != POSITIVEINFINITY) {
                magnitude += 1;
            }
        } else {
            magnitude -= 1;
        }
        long signbit = bits & SIGN;
        return Double.longBitsToDouble(magnitude | signbit);
    }
    
    private static double[] doubleArraySize(double[] array) {
        int oldSize = array.length;
        double[] newArray = new double[oldSize * 2];
        System.arraycopy(array, 0, newArray, 0, oldSize);
        return newArray;
    }
    
    private String[] doubleArraySize(String[] array) {
        int oldSize = array.length;
        String[] newArray = new String[oldSize * 2];
        System.arraycopy(array, 0, newArray, 0, oldSize);
        return newArray;
    }
}
