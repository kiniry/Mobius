package java.lang.reflect;

import java.lang.annotation.Annotation;

public interface AnnotatedElement {
    
    boolean isAnnotationPresent(Class annotationType);
    
    Annotation getAnnotation(Class annotationType);
    
    Annotation[] getAnnotations();
    
    Annotation[] getDeclaredAnnotations();
}
