package java.util;

public class IllegalFormatCodePointException extends IllegalFormatException {
    private static final long serialVersionUID = 19080630L;
    private int c;
    
    public IllegalFormatCodePointException(int c) {
        
        this.c = c;
    }
    
    public int getCodePoint() {
        return c;
    }
    
    public String getMessage() {
        return String.format("Code point = %c", new Object[]{Integer.valueOf(c)});
    }
}
