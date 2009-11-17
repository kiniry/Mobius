package java.text;

public class ParseException extends Exception {
    
    public ParseException(String s, int errorOffset) {
        super(s);
        this.errorOffset = errorOffset;
    }
    
    public int getErrorOffset() {
        return errorOffset;
    }
    private int errorOffset;
}
