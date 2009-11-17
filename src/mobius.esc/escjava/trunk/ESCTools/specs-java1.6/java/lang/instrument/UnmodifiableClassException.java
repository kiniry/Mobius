package java.lang.instrument;

public class UnmodifiableClassException extends Exception {
    
    public UnmodifiableClassException() {
        
    }
    
    public UnmodifiableClassException(String s) {
        super(s);
    }
}
