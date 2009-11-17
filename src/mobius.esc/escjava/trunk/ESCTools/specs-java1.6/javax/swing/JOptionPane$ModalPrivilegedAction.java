package javax.swing;

import java.lang.reflect.Method;
import java.security.PrivilegedAction;
import javax.accessibility.*;

class JOptionPane$ModalPrivilegedAction implements PrivilegedAction {
    private Class clazz;
    private String methodName;
    
    public JOptionPane$ModalPrivilegedAction(Class clazz, String methodName) {
        
        this.clazz = clazz;
        this.methodName = methodName;
    }
    
    public Object run() {
        Method method = null;
        try {
            method = clazz.getDeclaredMethod(methodName, null);
        } catch (NoSuchMethodException ex) {
        }
        if (method != null) {
            method.setAccessible(true);
        }
        return method;
    }
}
