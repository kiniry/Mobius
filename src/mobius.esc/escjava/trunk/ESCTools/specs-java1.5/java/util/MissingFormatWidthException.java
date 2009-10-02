package java.util;

public class MissingFormatWidthException extends IllegalFormatException {
    private static final long serialVersionUID = 15560123L;
    private String s;
    
    public MissingFormatWidthException(String s) {
        
        if (s == null) throw new NullPointerException();
        this.s = s;
    }
    
    public String getFormatSpecifier() {
        return s;
    }
    
    public String getMessage() {
        return s;
    }
}
