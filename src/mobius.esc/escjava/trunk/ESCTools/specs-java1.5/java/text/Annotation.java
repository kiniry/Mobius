package java.text;

public class Annotation {
    
    public Annotation(Object value) {
        
        this.value = value;
    }
    
    public Object getValue() {
        return value;
    }
    
    public String toString() {
        return getClass().getName() + "[value=" + value + "]";
    }
    private Object value;
}
