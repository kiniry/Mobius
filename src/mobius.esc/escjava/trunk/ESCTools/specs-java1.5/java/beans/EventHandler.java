package java.beans;

import java.lang.reflect.InvocationHandler;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Proxy;
import java.lang.reflect.Method;
import java.security.AccessControlContext;
import java.security.AccessController;
import sun.reflect.misc.MethodUtil;

public class EventHandler implements InvocationHandler {
    
    /*synthetic*/ static Object access$000(EventHandler x0, Object x1, Method x2, Object[] x3) {
        return x0.invokeInternal(x1, x2, x3);
    }
    private static Object[] empty = new Object[]{};
    private Object target;
    private Method targetMethod;
    private String action;
    private String eventPropertyName;
    private String listenerMethodName;
    private AccessControlContext acc;
    
    public EventHandler(Object target, String action, String eventPropertyName, String listenerMethodName) {
        
        this.acc = AccessController.getContext();
        this.target = target;
        this.action = action;
        this.eventPropertyName = eventPropertyName;
        this.listenerMethodName = listenerMethodName;
    }
    
    public Object getTarget() {
        return target;
    }
    
    public String getAction() {
        return action;
    }
    
    public String getEventPropertyName() {
        return eventPropertyName;
    }
    
    public String getListenerMethodName() {
        return listenerMethodName;
    }
    
    private Object applyGetters(Object target, String getters) {
        if (getters == null || getters.equals("")) {
            return target;
        }
        int firstDot = getters.indexOf('.');
        if (firstDot == -1) {
            firstDot = getters.length();
        }
        String first = getters.substring(0, firstDot);
        String rest = getters.substring(Math.min(firstDot + 1, getters.length()));
        try {
            Method getter = ReflectionUtils.getMethod(target.getClass(), "get" + NameGenerator.capitalize(first), new Class[]{});
            if (getter == null) {
                getter = ReflectionUtils.getMethod(target.getClass(), "is" + NameGenerator.capitalize(first), new Class[]{});
            }
            if (getter == null) {
                getter = ReflectionUtils.getMethod(target.getClass(), first, new Class[]{});
            }
            if (getter == null) {
                throw new RuntimeException("No method called: " + first + " defined on " + target);
            }
            Object newTarget = MethodUtil.invoke(getter, target, new Object[]{});
            return applyGetters(newTarget, rest);
        } catch (Throwable e) {
            throw new RuntimeException("Failed to call method: " + first + " on " + target, e);
        }
    }
    
    public Object invoke(final Object proxy, final Method method, final Object[] arguments) {
        return AccessController.doPrivileged(new EventHandler$1(this, proxy, method, arguments), acc);
    }
    
    private Object invokeInternal(Object proxy, Method method, Object[] arguments) {
        String methodName = method.getName();
        if (method.getDeclaringClass() == Object.class) {
            if (methodName.equals("hashCode")) {
                return new Integer(System.identityHashCode(proxy));
            } else if (methodName.equals("equals")) {
                return (proxy == arguments[0] ? Boolean.TRUE : Boolean.FALSE);
            } else if (methodName.equals("toString")) {
                return proxy.getClass().getName() + '@' + Integer.toHexString(proxy.hashCode());
            }
        }
        if (listenerMethodName == null || listenerMethodName.equals(methodName)) {
            Class[] argTypes = null;
            Object[] newArgs = null;
            if (eventPropertyName == null) {
                newArgs = new Object[]{};
                argTypes = new Class[]{};
            } else {
                Object input = applyGetters(arguments[0], getEventPropertyName());
                newArgs = new Object[]{input};
                argTypes = new Class[]{input.getClass()};
            }
            try {
                if (targetMethod == null) {
                    targetMethod = ReflectionUtils.getMethod(target.getClass(), action, argTypes);
                }
                if (targetMethod == null) {
                    targetMethod = ReflectionUtils.getMethod(target.getClass(), "set" + NameGenerator.capitalize(action), argTypes);
                }
                if (targetMethod == null) {
                    throw new RuntimeException("No method called: " + action + " on class " + target.getClass() + " with argument " + argTypes[0]);
                }
                return MethodUtil.invoke(targetMethod, target, newArgs);
            } catch (IllegalAccessException ex) {
                throw new RuntimeException(ex);
            } catch (InvocationTargetException ex) {
                throw new RuntimeException(ex.getTargetException());
            }
        }
        return null;
    }
    
    public static Object create(Class listenerInterface, Object target, String action) {
        return create(listenerInterface, target, action, null, null);
    }
    
    public static Object create(Class listenerInterface, Object target, String action, String eventPropertyName) {
        return create(listenerInterface, target, action, eventPropertyName, null);
    }
    
    public static Object create(Class listenerInterface, Object target, String action, String eventPropertyName, String listenerMethodName) {
        return (Object)Proxy.newProxyInstance(target.getClass().getClassLoader(), new Class[]{listenerInterface}, new EventHandler(target, action, eventPropertyName, listenerMethodName));
    }
}
