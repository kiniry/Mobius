package java.text;

public final class StringCharacterIterator implements CharacterIterator {
    private String text;
    private int begin;
    private int end;
    private int pos;
    
    public StringCharacterIterator(String text) {
        this(text, 0);
    }
    
    public StringCharacterIterator(String text, int pos) {
        this(text, 0, text.length(), pos);
    }
    
    public StringCharacterIterator(String text, int begin, int end, int pos) {
        
        if (text == null) throw new NullPointerException();
        this.text = text;
        if (begin < 0 || begin > end || end > text.length()) throw new IllegalArgumentException("Invalid substring range");
        if (pos < begin || pos > end) throw new IllegalArgumentException("Invalid position");
        this.begin = begin;
        this.end = end;
        this.pos = pos;
    }
    
    public void setText(String text) {
        if (text == null) throw new NullPointerException();
        this.text = text;
        this.begin = 0;
        this.end = text.length();
        this.pos = 0;
    }
    
    public char first() {
        pos = begin;
        return current();
    }
    
    public char last() {
        if (end != begin) {
            pos = end - 1;
        } else {
            pos = end;
        }
        return current();
    }
    
    public char setIndex(int p) {
        if (p < begin || p > end) throw new IllegalArgumentException("Invalid index");
        pos = p;
        return current();
    }
    
    public char current() {
        if (pos >= begin && pos < end) {
            return text.charAt(pos);
        } else {
            return DONE;
        }
    }
    
    public char next() {
        if (pos < end - 1) {
            pos++;
            return text.charAt(pos);
        } else {
            pos = end;
            return DONE;
        }
    }
    
    public char previous() {
        if (pos > begin) {
            pos--;
            return text.charAt(pos);
        } else {
            return DONE;
        }
    }
    
    public int getBeginIndex() {
        return begin;
    }
    
    public int getEndIndex() {
        return end;
    }
    
    public int getIndex() {
        return pos;
    }
    
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof StringCharacterIterator)) return false;
        StringCharacterIterator that = (StringCharacterIterator)(StringCharacterIterator)obj;
        if (hashCode() != that.hashCode()) return false;
        if (!text.equals(that.text)) return false;
        if (pos != that.pos || begin != that.begin || end != that.end) return false;
        return true;
    }
    
    public int hashCode() {
        return text.hashCode() ^ pos ^ begin ^ end;
    }
    
    public Object clone() {
        try {
            StringCharacterIterator other = (StringCharacterIterator)(StringCharacterIterator)super.clone();
            return other;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
}
