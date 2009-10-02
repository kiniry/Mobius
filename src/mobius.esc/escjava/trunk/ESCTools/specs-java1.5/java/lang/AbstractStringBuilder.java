package java.lang;

import sun.misc.FloatingDecimal;

abstract class AbstractStringBuilder implements Appendable, CharSequence {
    char[] value;
    int count;
    
    AbstractStringBuilder() {
        
    }
    
    AbstractStringBuilder(int capacity) {
        
        value = new char[capacity];
    }
    
    public int length() {
        return count;
    }
    
    public int capacity() {
        return value.length;
    }
    
    public void ensureCapacity(int minimumCapacity) {
        if (minimumCapacity > value.length) {
            expandCapacity(minimumCapacity);
        }
    }
    
    void expandCapacity(int minimumCapacity) {
        int newCapacity = (value.length + 1) * 2;
        if (newCapacity < 0) {
            newCapacity = Integer.MAX_VALUE;
        } else if (minimumCapacity > newCapacity) {
            newCapacity = minimumCapacity;
        }
        char[] newValue = new char[newCapacity];
        System.arraycopy(value, 0, newValue, 0, count);
        value = newValue;
    }
    
    public void trimToSize() {
        if (count < value.length) {
            char[] newValue = new char[count];
            System.arraycopy(value, 0, newValue, 0, count);
            this.value = newValue;
        }
    }
    
    public void setLength(int newLength) {
        if (newLength < 0) throw new StringIndexOutOfBoundsException(newLength);
        if (newLength > value.length) expandCapacity(newLength);
        if (count < newLength) {
            for (; count < newLength; count++) value[count] = '\000';
        } else {
            count = newLength;
        }
    }
    
    public char charAt(int index) {
        if ((index < 0) || (index >= count)) throw new StringIndexOutOfBoundsException(index);
        return value[index];
    }
    
    public int codePointAt(int index) {
        if ((index < 0) || (index >= count)) {
            throw new StringIndexOutOfBoundsException(index);
        }
        return Character.codePointAt(value, index);
    }
    
    public int codePointBefore(int index) {
        int i = index - 1;
        if ((i < 0) || (i >= count)) {
            throw new StringIndexOutOfBoundsException(index);
        }
        return Character.codePointBefore(value, index);
    }
    
    public int codePointCount(int beginIndex, int endIndex) {
        if (beginIndex < 0 || endIndex > count || beginIndex > endIndex) {
            throw new IndexOutOfBoundsException();
        }
        return Character.codePointCountImpl(value, beginIndex, endIndex - beginIndex);
    }
    
    public int offsetByCodePoints(int index, int codePointOffset) {
        if (index < 0 || index > count) {
            throw new IndexOutOfBoundsException();
        }
        return Character.offsetByCodePointsImpl(value, 0, count, index, codePointOffset);
    }
    
    public void getChars(int srcBegin, int srcEnd, char[] dst, int dstBegin) {
        if (srcBegin < 0) throw new StringIndexOutOfBoundsException(srcBegin);
        if ((srcEnd < 0) || (srcEnd > count)) throw new StringIndexOutOfBoundsException(srcEnd);
        if (srcBegin > srcEnd) throw new StringIndexOutOfBoundsException("srcBegin > srcEnd");
        System.arraycopy(value, srcBegin, dst, dstBegin, srcEnd - srcBegin);
    }
    
    public void setCharAt(int index, char ch) {
        if ((index < 0) || (index >= count)) throw new StringIndexOutOfBoundsException(index);
        value[index] = ch;
    }
    
    public AbstractStringBuilder append(Object obj) {
        return append(String.valueOf(obj));
    }
    
    public AbstractStringBuilder append(String str) {
        if (str == null) str = "null";
        int len = str.length();
        if (len == 0) return this;
        int newCount = count + len;
        if (newCount > value.length) expandCapacity(newCount);
        str.getChars(0, len, value, count);
        count = newCount;
        return this;
    }
    
    public AbstractStringBuilder append(StringBuffer sb) {
        if (sb == null) return append("null");
        int len = sb.length();
        int newCount = count + len;
        if (newCount > value.length) expandCapacity(newCount);
        sb.getChars(0, len, value, count);
        count = newCount;
        return this;
    }
    
    public AbstractStringBuilder append(CharSequence s) {
        if (s == null) s = "null";
        if (s instanceof String) return this.append((String)(String)s);
        if (s instanceof StringBuffer) return this.append((StringBuffer)(StringBuffer)s);
        return this.append(s, 0, s.length());
    }
    
    public AbstractStringBuilder append(CharSequence s, int start, int end) {
        if (s == null) s = "null";
        if ((start < 0) || (end < 0) || (start > end) || (end > s.length())) throw new IndexOutOfBoundsException("start " + start + ", end " + end + ", s.length() " + s.length());
        int len = end - start;
        if (len == 0) return this;
        int newCount = count + len;
        if (newCount > value.length) expandCapacity(newCount);
        for (int i = start; i < end; i++) value[count++] = s.charAt(i);
        count = newCount;
        return this;
    }
    
    public AbstractStringBuilder append(char[] str) {
        int newCount = count + str.length;
        if (newCount > value.length) expandCapacity(newCount);
        System.arraycopy(str, 0, value, count, str.length);
        count = newCount;
        return this;
    }
    
    public AbstractStringBuilder append(char[] str, int offset, int len) {
        int newCount = count + len;
        if (newCount > value.length) expandCapacity(newCount);
        System.arraycopy(str, offset, value, count, len);
        count = newCount;
        return this;
    }
    
    public AbstractStringBuilder append(boolean b) {
        if (b) {
            int newCount = count + 4;
            if (newCount > value.length) expandCapacity(newCount);
            value[count++] = 't';
            value[count++] = 'r';
            value[count++] = 'u';
            value[count++] = 'e';
        } else {
            int newCount = count + 5;
            if (newCount > value.length) expandCapacity(newCount);
            value[count++] = 'f';
            value[count++] = 'a';
            value[count++] = 'l';
            value[count++] = 's';
            value[count++] = 'e';
        }
        return this;
    }
    
    public AbstractStringBuilder append(char c) {
        int newCount = count + 1;
        if (newCount > value.length) expandCapacity(newCount);
        value[count++] = c;
        return this;
    }
    
    public AbstractStringBuilder append(int i) {
        if (i == Integer.MIN_VALUE) {
            append("-2147483648");
            return this;
        }
        int appendedLength = (i < 0) ? stringSizeOfInt(-i) + 1 : stringSizeOfInt(i);
        int spaceNeeded = count + appendedLength;
        if (spaceNeeded > value.length) expandCapacity(spaceNeeded);
        Integer.getChars(i, spaceNeeded, value);
        count = spaceNeeded;
        return this;
    }
    static final int[] sizeTable = {9, 99, 999, 9999, 99999, 999999, 9999999, 99999999, 999999999, Integer.MAX_VALUE};
    
    static int stringSizeOfInt(int x) {
        for (int i = 0; ; i++) if (x <= sizeTable[i]) return i + 1;
    }
    
    public AbstractStringBuilder append(long l) {
        if (l == Long.MIN_VALUE) {
            append("-9223372036854775808");
            return this;
        }
        int appendedLength = (l < 0) ? stringSizeOfLong(-l) + 1 : stringSizeOfLong(l);
        int spaceNeeded = count + appendedLength;
        if (spaceNeeded > value.length) expandCapacity(spaceNeeded);
        Long.getChars(l, spaceNeeded, value);
        count = spaceNeeded;
        return this;
    }
    
    static int stringSizeOfLong(long x) {
        long p = 10;
        for (int i = 1; i < 19; i++) {
            if (x < p) return i;
            p = 10 * p;
        }
        return 19;
    }
    
    public AbstractStringBuilder append(float f) {
        new FloatingDecimal(f).appendTo(this);
        return this;
    }
    
    public AbstractStringBuilder append(double d) {
        new FloatingDecimal(d).appendTo(this);
        return this;
    }
    
    public AbstractStringBuilder delete(int start, int end) {
        if (start < 0) throw new StringIndexOutOfBoundsException(start);
        if (end > count) end = count;
        if (start > end) throw new StringIndexOutOfBoundsException();
        int len = end - start;
        if (len > 0) {
            System.arraycopy(value, start + len, value, start, count - end);
            count -= len;
        }
        return this;
    }
    
    public AbstractStringBuilder appendCodePoint(int codePoint) {
        if (!Character.isValidCodePoint(codePoint)) {
            throw new IllegalArgumentException();
        }
        int n = 1;
        if (codePoint >= Character.MIN_SUPPLEMENTARY_CODE_POINT) {
            n++;
        }
        int newCount = count + n;
        if (newCount > value.length) {
            expandCapacity(newCount);
        }
        if (n == 1) {
            value[count++] = (char)codePoint;
        } else {
            Character.toSurrogates(codePoint, value, count);
            count += n;
        }
        return this;
    }
    
    public AbstractStringBuilder deleteCharAt(int index) {
        if ((index < 0) || (index >= count)) throw new StringIndexOutOfBoundsException(index);
        System.arraycopy(value, index + 1, value, index, count - index - 1);
        count--;
        return this;
    }
    
    public AbstractStringBuilder replace(int start, int end, String str) {
        if (start < 0) throw new StringIndexOutOfBoundsException(start);
        if (start > count) throw new StringIndexOutOfBoundsException("start > length()");
        if (start > end) throw new StringIndexOutOfBoundsException("start > end");
        if (end > count) end = count;
        if (end > count) end = count;
        int len = str.length();
        int newCount = count + len - (end - start);
        if (newCount > value.length) expandCapacity(newCount);
        System.arraycopy(value, end, value, start + len, count - end);
        str.getChars(value, start);
        count = newCount;
        return this;
    }
    
    public String substring(int start) {
        return substring(start, count);
    }
    
    public CharSequence subSequence(int start, int end) {
        return substring(start, end);
    }
    
    public String substring(int start, int end) {
        if (start < 0) throw new StringIndexOutOfBoundsException(start);
        if (end > count) throw new StringIndexOutOfBoundsException(end);
        if (start > end) throw new StringIndexOutOfBoundsException(end - start);
        return new String(value, start, end - start);
    }
    
    public AbstractStringBuilder insert(int index, char[] str, int offset, int len) {
        if ((index < 0) || (index > length())) throw new StringIndexOutOfBoundsException(index);
        if ((offset < 0) || (len < 0) || (offset > str.length - len)) throw new StringIndexOutOfBoundsException("offset " + offset + ", len " + len + ", str.length " + str.length);
        int newCount = count + len;
        if (newCount > value.length) expandCapacity(newCount);
        System.arraycopy(value, index, value, index + len, count - index);
        System.arraycopy(str, offset, value, index, len);
        count = newCount;
        return this;
    }
    
    public AbstractStringBuilder insert(int offset, Object obj) {
        return insert(offset, String.valueOf(obj));
    }
    
    public AbstractStringBuilder insert(int offset, String str) {
        if ((offset < 0) || (offset > length())) throw new StringIndexOutOfBoundsException(offset);
        if (str == null) str = "null";
        int len = str.length();
        int newCount = count + len;
        if (newCount > value.length) expandCapacity(newCount);
        System.arraycopy(value, offset, value, offset + len, count - offset);
        str.getChars(value, offset);
        count = newCount;
        return this;
    }
    
    public AbstractStringBuilder insert(int offset, char[] str) {
        if ((offset < 0) || (offset > length())) throw new StringIndexOutOfBoundsException(offset);
        int len = str.length;
        int newCount = count + len;
        if (newCount > value.length) expandCapacity(newCount);
        System.arraycopy(value, offset, value, offset + len, count - offset);
        System.arraycopy(str, 0, value, offset, len);
        count = newCount;
        return this;
    }
    
    public AbstractStringBuilder insert(int dstOffset, CharSequence s) {
        if (s == null) s = "null";
        if (s instanceof String) return this.insert(dstOffset, (String)(String)s);
        return this.insert(dstOffset, s, 0, s.length());
    }
    
    public AbstractStringBuilder insert(int dstOffset, CharSequence s, int start, int end) {
        if (s == null) s = "null";
        if ((dstOffset < 0) || (dstOffset > this.length())) throw new IndexOutOfBoundsException("dstOffset " + dstOffset);
        if ((start < 0) || (end < 0) || (start > end) || (end > s.length())) throw new IndexOutOfBoundsException("start " + start + ", end " + end + ", s.length() " + s.length());
        int len = end - start;
        if (len == 0) return this;
        int newCount = count + len;
        if (newCount > value.length) expandCapacity(newCount);
        System.arraycopy(value, dstOffset, value, dstOffset + len, count - dstOffset);
        for (int i = start; i < end; i++) value[dstOffset++] = s.charAt(i);
        count = newCount;
        return this;
    }
    
    public AbstractStringBuilder insert(int offset, boolean b) {
        return insert(offset, String.valueOf(b));
    }
    
    public AbstractStringBuilder insert(int offset, char c) {
        int newCount = count + 1;
        if (newCount > value.length) expandCapacity(newCount);
        System.arraycopy(value, offset, value, offset + 1, count - offset);
        value[offset] = c;
        count = newCount;
        return this;
    }
    
    public AbstractStringBuilder insert(int offset, int i) {
        return insert(offset, String.valueOf(i));
    }
    
    public AbstractStringBuilder insert(int offset, long l) {
        return insert(offset, String.valueOf(l));
    }
    
    public AbstractStringBuilder insert(int offset, float f) {
        return insert(offset, String.valueOf(f));
    }
    
    public AbstractStringBuilder insert(int offset, double d) {
        return insert(offset, String.valueOf(d));
    }
    
    public int indexOf(String str) {
        return indexOf(str, 0);
    }
    
    public int indexOf(String str, int fromIndex) {
        return String.indexOf(value, 0, count, str.toCharArray(), 0, str.length(), fromIndex);
    }
    
    public int lastIndexOf(String str) {
        return lastIndexOf(str, count);
    }
    
    public int lastIndexOf(String str, int fromIndex) {
        return String.lastIndexOf(value, 0, count, str.toCharArray(), 0, str.length(), fromIndex);
    }
    
    public AbstractStringBuilder reverse() {
        boolean hasSurrogate = false;
        int n = count - 1;
        for (int j = (n - 1) >> 1; j >= 0; --j) {
            char temp = value[j];
            char temp2 = value[n - j];
            if (!hasSurrogate) {
                hasSurrogate = (temp >= Character.MIN_SURROGATE && temp <= Character.MAX_SURROGATE) || (temp2 >= Character.MIN_SURROGATE && temp2 <= Character.MAX_SURROGATE);
            }
            value[j] = temp2;
            value[n - j] = temp;
        }
        if (hasSurrogate) {
            for (int i = 0; i < count - 1; i++) {
                char c2 = value[i];
                if (Character.isLowSurrogate(c2)) {
                    char c1 = value[i + 1];
                    if (Character.isHighSurrogate(c1)) {
                        value[i++] = c1;
                        value[i] = c2;
                    }
                }
            }
        }
        return this;
    }
    
    public abstract String toString();
    
    final char[] getValue() {
        return value;
    }
    
    /*synthetic*/ public Appendable append(char x0) throws .java.io.IOException {
        return this.append(x0);
    }
    
    /*synthetic*/ public Appendable append(CharSequence x0, int x1, int x2) throws .java.io.IOException {
        return this.append(x0, x1, x2);
    }
    
    /*synthetic*/ public Appendable append(CharSequence x0) throws .java.io.IOException {
        return this.append(x0);
    }
}
