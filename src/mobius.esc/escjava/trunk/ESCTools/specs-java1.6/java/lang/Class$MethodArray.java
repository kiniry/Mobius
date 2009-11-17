package java.lang;

import java.lang.reflect.Method;
import sun.reflect.annotation.*;

class Class$MethodArray {
    private Method[] methods;
    private int length;
    
    Class$MethodArray() {
        
        methods = new Method[20];
        length = 0;
    }
    
    void add(Method m) {
        if (length == methods.length) {
            Method[] newMethods = new Method[2 * methods.length];
            System.arraycopy(methods, 0, newMethods, 0, methods.length);
            methods = newMethods;
        }
        methods[length++] = m;
    }
    
    void addAll(Method[] ma) {
        for (int i = 0; i < ma.length; i++) {
            add(ma[i]);
        }
    }
    
    void addAll(Class$MethodArray ma) {
        for (int i = 0; i < ma.length(); i++) {
            add(ma.get(i));
        }
    }
    
    void addIfNotPresent(Method newMethod) {
        for (int i = 0; i < length; i++) {
            Method m = methods[i];
            if (m == newMethod || (m != null && m.equals(newMethod))) {
                return;
            }
        }
        add(newMethod);
    }
    
    void addAllIfNotPresent(Class$MethodArray newMethods) {
        for (int i = 0; i < newMethods.length(); i++) {
            Method m = newMethods.get(i);
            if (m != null) {
                addIfNotPresent(m);
            }
        }
    }
    
    int length() {
        return length;
    }
    
    Method get(int i) {
        return methods[i];
    }
    
    void removeByNameAndSignature(Method toRemove) {
        for (int i = 0; i < length; i++) {
            Method m = methods[i];
            if (m != null && m.getReturnType() == toRemove.getReturnType() && m.getName() == toRemove.getName() && Class.access$100(m.getParameterTypes(), toRemove.getParameterTypes())) {
                methods[i] = null;
            }
        }
    }
    
    void compactAndTrim() {
        int newPos = 0;
        for (int pos = 0; pos < length; pos++) {
            Method m = methods[pos];
            if (m != null) {
                if (pos != newPos) {
                    methods[newPos] = m;
                }
                newPos++;
            }
        }
        if (newPos != methods.length) {
            Method[] newMethods = new Method[newPos];
            System.arraycopy(methods, 0, newMethods, 0, newPos);
            methods = newMethods;
        }
    }
    
    Method[] getArray() {
        return methods;
    }
}
