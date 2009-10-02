package java.lang.annotation;

public class IncompleteAnnotationException extends RuntimeException {
    private Class annotationType;
    private String elementName;
    
    public IncompleteAnnotationException(Class annotationType, String elementName) {
        super(annotationType.getName() + " missing element " + elementName);
        this.annotationType = annotationType;
        this.elementName = elementName;
    }
    
    public Class annotationType() {
        return annotationType;
    }
    
    public String elementName() {
        return elementName;
    }
}
