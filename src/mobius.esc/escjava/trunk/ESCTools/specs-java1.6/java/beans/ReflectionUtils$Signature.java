package java.beans;

import java.util.*;

class ReflectionUtils$Signature {
    private Class targetClass;
    private String methodName;
    private Class[] argClasses;
    private volatile int hashCode = 0;
    
    public ReflectionUtils$Signature(Class targetClass, String methodName, Class[] argClasses) {
        
        this.targetClass = targetClass;
        this.methodName = methodName;
        this.argClasses = argClasses;
    }
    
    public boolean equals(Object o2) {
        if (this == o2) {
            return true;
        }
        ReflectionUtils$Signature that = (ReflectionUtils$Signature)(ReflectionUtils$Signature)o2;
        if (!(targetClass == that.targetClass)) {
            return false;
        }
        if (!(methodName.equals(that.methodName))) {
            return false;
        }
        if (argClasses.length != that.argClasses.length) {
            return false;
        }
        for (int i = 0; i < argClasses.length; i++) {
            if (!(argClasses[i] == that.argClasses[i])) {
                return false;
            }
        }
        return true;
    }
    
    public int hashCode() {
        if (hashCode == 0) {
            int result = 17;
            result = 37 * result + targetClass.hashCode();
            result = 37 * result + methodName.hashCode();
            if (argClasses != null) {
                for (int i = 0; i < argClasses.length; i++) {
                    result = 37 * result + ((argClasses[i] == null) ? 0 : argClasses[i].hashCode());
                }
            }
            hashCode = result;
        }
        return hashCode;
    }
}
