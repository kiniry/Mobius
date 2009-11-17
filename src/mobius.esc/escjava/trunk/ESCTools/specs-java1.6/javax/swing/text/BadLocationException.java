package javax.swing.text;

public class BadLocationException extends Exception {
    
    public BadLocationException(String s, int offs) {
        super(s);
        this.offs = offs;
    }
    
    public int offsetRequested() {
        return offs;
    }
    private int offs;
}
