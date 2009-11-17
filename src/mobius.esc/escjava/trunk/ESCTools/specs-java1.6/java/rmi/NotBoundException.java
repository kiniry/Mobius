package java.rmi;

public class NotBoundException extends java.lang.Exception {
    private static final long serialVersionUID = -1857741824849069317L;
    
    public NotBoundException() {
        
    }
    
    public NotBoundException(String s) {
        super(s);
    }
}
