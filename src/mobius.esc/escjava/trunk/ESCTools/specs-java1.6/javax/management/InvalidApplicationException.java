package javax.management;

public class InvalidApplicationException extends Exception {
    private static final long serialVersionUID = -3048022274675537269L;
    private Object val;
    
    public InvalidApplicationException(Object val) {
        
        this.val = val;
    }
}
