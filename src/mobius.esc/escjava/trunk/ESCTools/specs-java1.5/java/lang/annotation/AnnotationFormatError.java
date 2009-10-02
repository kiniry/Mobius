package java.lang.annotation;

public class AnnotationFormatError extends Error {
    
    public AnnotationFormatError(String message) {
        super(message);
    }
    
    public AnnotationFormatError(String message, Throwable cause) {
        super(message, cause);
    }
    
    public AnnotationFormatError(Throwable cause) {
        super(cause);
    }
}
