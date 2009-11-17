package java.util;

public class FormatFlagsConversionMismatchException extends IllegalFormatException {
    private static final long serialVersionUID = 19120414L;
    private String f;
    private char c;
    
    public FormatFlagsConversionMismatchException(String f, char c) {
        
        if (f == null) throw new NullPointerException();
        this.f = f;
        this.c = c;
    }
    
    public String getFlags() {
        return f;
    }
    
    public char getConversion() {
        return c;
    }
    
    public String getMessage() {
        return "Conversion = " + c + ", Flags = " + f;
    }
}
