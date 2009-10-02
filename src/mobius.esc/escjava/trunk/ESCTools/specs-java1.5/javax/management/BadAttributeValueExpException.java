package javax.management;

public class BadAttributeValueExpException extends Exception {
    private static final long serialVersionUID = -3105272988410493376L;
    private Object val;
    
    public BadAttributeValueExpException(Object val) {
        
        this.val = val;
    }
    
    public String toString() {
        return "BadAttributeValueException: " + val;
    }
}
