package javax.management;

import java.lang.reflect.Method;
import java.security.PrivilegedAction;

class MBeanInfo$ImmutabilityAction implements PrivilegedAction {
    private final Class subclass;
    private final Class immutableClass;
    
    MBeanInfo$ImmutabilityAction(Class subclass, Class immutableClass) {
        
        this.subclass = subclass;
        this.immutableClass = immutableClass;
    }
    
    public Object run() {
        Method[] methods = immutableClass.getMethods();
        for (int i = 0; i < methods.length; i++) {
            Method method = methods[i];
            String methodName = method.getName();
            if (methodName.startsWith("get") || methodName.startsWith("is")) {
                Class[] paramTypes = method.getParameterTypes();
                try {
                    Method submethod = subclass.getMethod(methodName, paramTypes);
                    if (!submethod.equals(method)) return Boolean.FALSE;
                } catch (NoSuchMethodException e) {
                    return Boolean.FALSE;
                }
            }
        }
        return Boolean.TRUE;
    }
}
