package java.lang;

public final class StringBuilder extends AbstractStringBuilder implements java.io.Serializable, CharSequence {
    static final long serialVersionUID = 4383685877147921099L;
    
    public StringBuilder() {
        super(16);
    }
    
    public StringBuilder(int capacity) {
        super(capacity);
    }
    
    public StringBuilder(String str) {
        super(str.length() + 16);
        append(str);
    }
    
    public StringBuilder(CharSequence seq) {
        this(seq.length() + 16);
        append(seq);
    }
    
    public StringBuilder append(Object obj) {
        return append(String.valueOf(obj));
    }
    
    public StringBuilder append(String str) {
        super.append(str);
        return this;
    }
    
    private StringBuilder append(StringBuilder sb) {
        if (sb == null) return append("null");
        int len = sb.length();
        int newcount = count + len;
        if (newcount > value.length) expandCapacity(newcount);
        sb.getChars(0, len, value, count);
        count = newcount;
        return this;
    }
    
    public StringBuilder append(StringBuffer sb) {
        super.append(sb);
        return this;
    }
    
    public StringBuilder append(CharSequence s) {
        if (s == null) s = "null";
        if (s instanceof String) return this.append((String)(String)s);
        if (s instanceof StringBuffer) return this.append((StringBuffer)(StringBuffer)s);
        if (s instanceof StringBuilder) return this.append((StringBuilder)(StringBuilder)s);
        return this.append(s, 0, s.length());
    }
    
    public StringBuilder append(CharSequence s, int start, int end) {
        super.append(s, start, end);
        return this;
    }
    
    public StringBuilder append(char[] str) {
        super.append(str);
        return this;
    }
    
    public StringBuilder append(char[] str, int offset, int len) {
        super.append(str, offset, len);
        return this;
    }
    
    public StringBuilder append(boolean b) {
        super.append(b);
        return this;
    }
    
    public StringBuilder append(char c) {
        super.append(c);
        return this;
    }
    
    public StringBuilder append(int i) {
        super.append(i);
        return this;
    }
    
    public StringBuilder append(long lng) {
        super.append(lng);
        return this;
    }
    
    public StringBuilder append(float f) {
        super.append(f);
        return this;
    }
    
    public StringBuilder append(double d) {
        super.append(d);
        return this;
    }
    
    public StringBuilder appendCodePoint(int codePoint) {
        super.appendCodePoint(codePoint);
        return this;
    }
    
    public StringBuilder delete(int start, int end) {
        super.delete(start, end);
        return this;
    }
    
    public StringBuilder deleteCharAt(int index) {
        super.deleteCharAt(index);
        return this;
    }
    
    public StringBuilder replace(int start, int end, String str) {
        super.replace(start, end, str);
        return this;
    }
    
    public StringBuilder insert(int index, char[] str, int offset, int len) {
        super.insert(index, str, offset, len);
        return this;
    }
    
    public StringBuilder insert(int offset, Object obj) {
        return insert(offset, String.valueOf(obj));
    }
    
    public StringBuilder insert(int offset, String str) {
        super.insert(offset, str);
        return this;
    }
    
    public StringBuilder insert(int offset, char[] str) {
        super.insert(offset, str);
        return this;
    }
    
    public StringBuilder insert(int dstOffset, CharSequence s) {
        if (s == null) s = "null";
        if (s instanceof String) return this.insert(dstOffset, (String)(String)s);
        return this.insert(dstOffset, s, 0, s.length());
    }
    
    public StringBuilder insert(int dstOffset, CharSequence s, int start, int end) {
        super.insert(dstOffset, s, start, end);
        return this;
    }
    
    public StringBuilder insert(int offset, boolean b) {
        super.insert(offset, b);
        return this;
    }
    
    public StringBuilder insert(int offset, char c) {
        super.insert(offset, c);
        return this;
    }
    
    public StringBuilder insert(int offset, int i) {
        return insert(offset, String.valueOf(i));
    }
    
    public StringBuilder insert(int offset, long l) {
        return insert(offset, String.valueOf(l));
    }
    
    public StringBuilder insert(int offset, float f) {
        return insert(offset, String.valueOf(f));
    }
    
    public StringBuilder insert(int offset, double d) {
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
    
    public StringBuilder reverse() {
        super.reverse();
        return this;
    }
    
    public String toString() {
        return new String(value, 0, count);
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        s.defaultWriteObject();
        s.writeInt(count);
        s.writeObject(value);
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        count = s.readInt();
        value = (char[])(char[])s.readObject();
    }
    
    /*synthetic public AbstractStringBuilder reverse() {
        return this.reverse();
    }
    
    /*synthetic public AbstractStringBuilder insert(int x0, double x1) {
        return this.insert(x0, x1);
    }
    
    /*synthetic public AbstractStringBuilder insert(int x0, float x1) {
        return this.insert(x0, x1);
    }
    
    /*synthetic public AbstractStringBuilder insert(int x0, long x1) {
        return this.insert(x0, x1);
    }
    
    /*synthetic public AbstractStringBuilder insert(int x0, int x1) {
        return this.insert(x0, x1);
    }
    
    /*synthetic public AbstractStringBuilder insert(int x0, char x1) {
        return this.insert(x0, x1);
    }
    
    /*synthetic public AbstractStringBuilder insert(int x0, boolean x1) {
        return this.insert(x0, x1);
    }
    
    /*synthetic public AbstractStringBuilder insert(int x0, CharSequence x1, int x2, int x3) {
        return this.insert(x0, x1, x2, x3);
    }
    
    /*synthetic public AbstractStringBuilder insert(int x0, CharSequence x1) {
        return this.insert(x0, x1);
    }
    
    /*synthetic public AbstractStringBuilder insert(int x0, char[] x1) {
        return this.insert(x0, x1);
    }
    
    /*synthetic public AbstractStringBuilder insert(int x0, String x1) {
        return this.insert(x0, x1);
    }
    
    /*synthetic public AbstractStringBuilder insert(int x0, Object x1) {
        return this.insert(x0, x1);
    }
    
    /*synthetic public AbstractStringBuilder insert(int x0, char[] x1, int x2, int x3) {
        return this.insert(x0, x1, x2, x3);
    }
    
    /*synthetic public AbstractStringBuilder replace(int x0, int x1, String x2) {
        return this.replace(x0, x1, x2);
    }
    
    /*synthetic public AbstractStringBuilder deleteCharAt(int x0) {
        return this.deleteCharAt(x0);
    }
    
    /*synthetic public AbstractStringBuilder appendCodePoint(int x0) {
        return this.appendCodePoint(x0);
    }
    
    /*synthetic public AbstractStringBuilder delete(int x0, int x1) {
        return this.delete(x0, x1);
    }
    
    /*synthetic public AbstractStringBuilder append(double x0) {
        return this.append(x0);
    }
    
    /*synthetic public AbstractStringBuilder append(float x0) {
        return this.append(x0);
    }
    
    /*synthetic public AbstractStringBuilder append(long x0) {
        return this.append(x0);
    }
    
    /*synthetic public AbstractStringBuilder append(int x0) {
        return this.append(x0);
    }
    
    /*synthetic public AbstractStringBuilder append(char x0) {
        return this.append(x0);
    }
    
    /*synthetic public AbstractStringBuilder append(boolean x0) {
        return this.append(x0);
    }
    
    /*synthetic public AbstractStringBuilder append(char[] x0, int x1, int x2) {
        return this.append(x0, x1, x2);
    }
    
    /*synthetic public AbstractStringBuilder append(char[] x0) {
        return this.append(x0);
    }
    
    /*synthetic public AbstractStringBuilder append(CharSequence x0, int x1, int x2) {
        return this.append(x0, x1, x2);
    }
    
    /*synthetic public AbstractStringBuilder append(CharSequence x0) {
        return this.append(x0);
    }
    
    /*synthetic public AbstractStringBuilder append(StringBuffer x0) {
        return this.append(x0);
    }
    
    /*synthetic public AbstractStringBuilder append(String x0) {
        return this.append(x0);
    }
    
    /*synthetic public AbstractStringBuilder append(Object x0) {
        return this.append(x0);
    }
    
    /*synthetic/ public Appendable append(char x0) throws java.io.IOException {
        return this.append(x0);
    }
    
    /*synthetic public Appendable append(CharSequence x0, int x1, int x2) throws .java.io.IOException {
        return this.append(x0, x1, x2);
    }
    
    /*synthetic public Appendable append(CharSequence x0) throws java.io.IOException {
        return this.append(x0);
    } */
}
