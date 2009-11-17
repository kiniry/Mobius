package java.rmi;

public class AlreadyBoundException extends java.lang.Exception {
    private static final long serialVersionUID = 9218657361741657110L;
    
    public AlreadyBoundException() {
        
    }
    
    public AlreadyBoundException(String s) {
        super(s);
    }
}
