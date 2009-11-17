package java.util;

public class IllegalFormatConversionException extends IllegalFormatException {
    private static final long serialVersionUID = 17000126L;
    private char c;
    private Class arg;
    
    public IllegalFormatConversionException(char c, Class arg) {
        
        if (arg == null) throw new NullPointerException();
        this.c = c;
        this.arg = arg;
    }
    
    public char getConversion() {
        return c;
    }
    
    public Class getArgumentClass() {
        return arg;
    }
    
    public String getMessage() {
        return String.format("%c != %s", new Object[]{Character.valueOf(c), arg.getName()});
    }
}
