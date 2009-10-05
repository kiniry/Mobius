package java.io;

public class CharArrayWriter extends Writer {
    protected char[] buf;
    protected int count;
    
    public CharArrayWriter() {
        this(32);
    }
    
    public CharArrayWriter(int initialSize) {
        
        if (initialSize < 0) {
            throw new IllegalArgumentException("Negative initial size: " + initialSize);
        }
        buf = new char[initialSize];
    }
    
    public void write(int c) {
        synchronized (lock) {
            int newcount = count + 1;
            if (newcount > buf.length) {
                char[] newbuf = new char[Math.max(buf.length << 1, newcount)];
                System.arraycopy(buf, 0, newbuf, 0, count);
                buf = newbuf;
            }
            buf[count] = (char)c;
            count = newcount;
        }
    }
    
    public void write(char[] c, int off, int len) {
        if ((off < 0) || (off > c.length) || (len < 0) || ((off + len) > c.length) || ((off + len) < 0)) {
            throw new IndexOutOfBoundsException();
        } else if (len == 0) {
            return;
        }
        synchronized (lock) {
            int newcount = count + len;
            if (newcount > buf.length) {
                char[] newbuf = new char[Math.max(buf.length << 1, newcount)];
                System.arraycopy(buf, 0, newbuf, 0, count);
                buf = newbuf;
            }
            System.arraycopy(c, off, buf, count, len);
            count = newcount;
        }
    }
    
    public void write(String str, int off, int len) {
        synchronized (lock) {
            int newcount = count + len;
            if (newcount > buf.length) {
                char[] newbuf = new char[Math.max(buf.length << 1, newcount)];
                System.arraycopy(buf, 0, newbuf, 0, count);
                buf = newbuf;
            }
            str.getChars(off, off + len, buf, count);
            count = newcount;
        }
    }
    
    public void writeTo(Writer out) throws IOException {
        synchronized (lock) {
            out.write(buf, 0, count);
        }
    }
    
    public CharArrayWriter append(CharSequence csq) {
        String s = (csq == null ? "null" : csq.toString());
        write(s, 0, s.length());
        return this;
    }
    
    public CharArrayWriter append(CharSequence csq, int start, int end) {
        String s = (csq == null ? "null" : csq).subSequence(start, end).toString();
        write(s, 0, s.length());
        return this;
    }
    
    public CharArrayWriter append(char c) {
        write(c);
        return this;
    }
    
    public void reset() {
        count = 0;
    }
    
    public char[] toCharArray() {
        synchronized (lock) {
            char[] newbuf = new char[count];
            System.arraycopy(buf, 0, newbuf, 0, count);
            return newbuf;
        }
    }
    
    public int size() {
        return count;
    }
    
    public String toString() {
        synchronized (lock) {
            return new String(buf, 0, count);
        }
    }
    
    public void flush() {
    }
    
    public void close() {
    }
    
    /*synthetic public Writer append(char x0) throws IOException {
        return this.append(x0);
    } */
    
    /*synthetic public Writer append(CharSequence x0, int x1, int x2) throws IOException {
        return this.append(x0, x1, x2);
    } */
    
    /*synthetic public Writer append(CharSequence x0) throws IOException {
        return this.append(x0);
    } */
    
    /*synthetic public Appendable append(char x0) throws IOException {
        return this.append(x0);
    } */
    
    /*synthetic public Appendable append(CharSequence x0, int x1, int x2) throws IOException {
        return this.append(x0, x1, x2);
    } */
    
    /*synthetic public Appendable append(CharSequence x0) throws IOException {
        return this.append(x0);
    } */
}
