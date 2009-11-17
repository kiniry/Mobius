package java.beans;

import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import com.sun.beans.ObjectHandler;
import sun.reflect.misc.MethodUtil;

public class Statement {
    private static Object[] emptyArray = new Object[]{};
    static ExceptionListener defaultExceptionListener = new Statement$1();
    Object target;
    String methodName;
    Object[] arguments;
    
    public Statement(Object target, String methodName, Object[] arguments) {
        
        this.target = target;
        this.methodName = methodName;
        this.arguments = (arguments == null) ? emptyArray : arguments;
    }
    
    public Object getTarget() {
        return target;
    }
    
    public String getMethodName() {
        return methodName;
    }
    
    public Object[] getArguments() {
        return arguments;
    }
    
    public void execute() throws Exception {
        invoke();
    }
    
    Object invoke() throws Exception {
        Object target = getTarget();
        String methodName = getMethodName();
        if (target == null || methodName == null) {
            throw new NullPointerException((target == null ? "target" : "methodName") + " should not be null");
        }
        Object[] arguments = getArguments();
        if (target == Class.class && methodName.equals("forName")) {
            return ObjectHandler.classForName((String)(String)arguments[0]);
        }
        Class[] argClasses = new Class[arguments.length];
        for (int i = 0; i < arguments.length; i++) {
            argClasses[i] = (arguments[i] == null) ? null : arguments[i].getClass();
        }
        AccessibleObject m = null;
        if (target instanceof Class) {
            if (methodName.equals("new")) {
                methodName = "newInstance";
            }
            if (methodName.equals("newInstance") && ((Class)(Class)target).isArray()) {
                Object result = Array.newInstance(((Class)(Class)target).getComponentType(), arguments.length);
                for (int i = 0; i < arguments.length; i++) {
                    Array.set(result, i, arguments[i]);
                }
                return result;
            }
            if (methodName.equals("newInstance") && arguments.length != 0) {
                if (target == Character.class && arguments.length == 1 && argClasses[0] == String.class) {
                    return new Character(((String)(String)arguments[0]).charAt(0));
                }
                m = ReflectionUtils.getConstructor((Class)(Class)target, argClasses);
            }
            if (m == null && target != Class.class) {
                m = ReflectionUtils.getMethod((Class)(Class)target, methodName, argClasses);
            }
            if (m == null) {
                m = ReflectionUtils.getMethod(Class.class, methodName, argClasses);
            }
        } else {
            if (target.getClass().isArray() && (methodName.equals("set") || methodName.equals("get"))) {
                int index = ((Integer)(Integer)arguments[0]).intValue();
                if (methodName.equals("get")) {
                    return Array.get(target, index);
                } else {
                    Array.set(target, index, arguments[1]);
                    return null;
                }
            }
            m = ReflectionUtils.getMethod(target.getClass(), methodName, argClasses);
        }
        if (m != null) {
            try {
                if (m instanceof Method) {
                    return MethodUtil.invoke((Method)(Method)m, target, arguments);
                } else {
                    return ((Constructor)(Constructor)m).newInstance(arguments);
                }
            } catch (IllegalAccessException iae) {
                throw new Exception("Statement cannot invoke: " + methodName + " on " + target.getClass(), iae);
            } catch (InvocationTargetException ite) {
                Throwable te = ite.getTargetException();
                if (te instanceof Exception) {
                    throw (Exception)(Exception)te;
                } else {
                    throw ite;
                }
            }
        }
        throw new NoSuchMethodException(toString());
    }
    
    String instanceName(Object instance) {
        if (instance == null) {
            return "null";
        } else if (instance.getClass() == String.class) {
            return "\"" + (String)(String)instance + "\"";
        } else {
            return NameGenerator.unqualifiedClassName(instance.getClass());
        }
    }
    
    public String toString() {
        Object target = getTarget();
        String methodName = getMethodName();
        Object[] arguments = getArguments();
        StringBuffer result = new StringBuffer(instanceName(target) + "." + methodName + "(");
        int n = arguments.length;
        for (int i = 0; i < n; i++) {
            result.append(instanceName(arguments[i]));
            if (i != n - 1) {
                result.append(", ");
            }
        }
        result.append(");");
        return result.toString();
    }
}
