package java.lang.reflect;

import java.security.AccessController;
import sun.reflect.ReflectionFactory;
import java.lang.annotation.Annotation;

public class AccessibleObject implements AnnotatedElement {
    private static final java.security.Permission ACCESS_PERMISSION = new ReflectPermission("suppressAccessChecks");
    
    public static void setAccessible(AccessibleObject[] array, boolean flag) throws SecurityException {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) sm.checkPermission(ACCESS_PERMISSION);
        for (int i = 0; i < array.length; i++) {
            setAccessible0(array[i], flag);
        }
    }
    
    public void setAccessible(boolean flag) throws SecurityException {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) sm.checkPermission(ACCESS_PERMISSION);
        setAccessible0(this, flag);
    }
    
    private static void setAccessible0(AccessibleObject obj, boolean flag) throws SecurityException {
        if (obj instanceof Constructor && flag == true) {
            Constructor c = (Constructor)(Constructor)obj;
            if (c.getDeclaringClass() == Class.class) {
                throw new SecurityException("Can not make a java.lang.Class constructor accessible");
            }
        }
        obj.override = flag;
    }
    
    public boolean isAccessible() {
        return override;
    }
    
    protected AccessibleObject() {
        
    }
    volatile Class securityCheckCache;
    boolean override;
    static final ReflectionFactory reflectionFactory = (ReflectionFactory)(ReflectionFactory)AccessController.doPrivileged(new sun.reflect.ReflectionFactory$GetReflectionFactoryAction());
    
    public Annotation getAnnotation(Class annotationClass) {
        throw new AssertionError("All subclasses should override this method");
    }
    
    public boolean isAnnotationPresent(Class annotationClass) {
        return getAnnotation(annotationClass) != null;
    }
    
    public Annotation[] getAnnotations() {
        return getDeclaredAnnotations();
    }
    
    public Annotation[] getDeclaredAnnotations() {
        throw new AssertionError("All subclasses should override this method");
    }
}
