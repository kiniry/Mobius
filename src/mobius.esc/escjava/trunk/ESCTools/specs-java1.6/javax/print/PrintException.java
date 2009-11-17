package javax.print;

public class PrintException extends Exception {
    
    public PrintException() {
        
    }
    
    public PrintException(String s) {
        super(s);
    }
    
    public PrintException(Exception e) {
        super(e);
    }
    
    public PrintException(String s, Exception e) {
        super(s, e);
    }
}
