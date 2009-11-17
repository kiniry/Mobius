package javax.management;

import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;

public class MBeanServerInvocationHandler implements InvocationHandler {
    
    public MBeanServerInvocationHandler(MBeanServerConnection connection, ObjectName objectName) {
        
        this.connection = connection;
        this.objectName = objectName;
    }
    
    public static Object newProxyInstance(MBeanServerConnection connection, ObjectName objectName, Class interfaceClass, boolean notificationBroadcaster) {
        final InvocationHandler handler = new MBeanServerInvocationHandler(connection, objectName);
        final Class[] interfaces;
        if (notificationBroadcaster) {
            interfaces = new Class[]{interfaceClass, NotificationEmitter.class};
        } else interfaces = new Class[]{interfaceClass};
        return Proxy.newProxyInstance(interfaceClass.getClassLoader(), interfaces, handler);
    }
    
    public Object invoke(Object proxy, Method method, Object[] args) throws Throwable {
        final Class methodClass = method.getDeclaringClass();
        if (methodClass.equals(NotificationBroadcaster.class) || methodClass.equals(NotificationEmitter.class)) return invokeBroadcasterMethod(proxy, method, args);
        final String methodName = method.getName();
        final Class[] paramTypes = method.getParameterTypes();
        final Class returnType = method.getReturnType();
        final int nargs = (args == null) ? 0 : args.length;
        if (methodName.startsWith("get") && methodName.length() > 3 && nargs == 0 && !returnType.equals(Void.TYPE)) {
            return connection.getAttribute(objectName, methodName.substring(3));
        }
        if (methodName.startsWith("is") && methodName.length() > 2 && nargs == 0 && (returnType.equals(Boolean.TYPE) || returnType.equals(Boolean.class))) {
            return connection.getAttribute(objectName, methodName.substring(2));
        }
        if (methodName.startsWith("set") && methodName.length() > 3 && nargs == 1 && returnType.equals(Void.TYPE)) {
            Attribute attr = new Attribute(methodName.substring(3), args[0]);
            connection.setAttribute(objectName, attr);
            return null;
        }
        final String[] signature = new String[paramTypes.length];
        for (int i = 0; i < paramTypes.length; i++) signature[i] = paramTypes[i].getName();
        try {
            return connection.invoke(objectName, methodName, args, signature);
        } catch (MBeanException e) {
            throw e.getTargetException();
        }
    }
    
    private Object invokeBroadcasterMethod(Object proxy, Method method, Object[] args) throws Exception {
        final String methodName = method.getName();
        final int nargs = (args == null) ? 0 : args.length;
        if (methodName.equals("addNotificationListener")) {
            if (nargs != 3) {
                final String msg = "Bad arg count to addNotificationListener: " + nargs;
                throw new IllegalArgumentException(msg);
            }
            NotificationListener listener = (NotificationListener)(NotificationListener)args[0];
            NotificationFilter filter = (NotificationFilter)(NotificationFilter)args[1];
            Object handback = args[2];
            connection.addNotificationListener(objectName, listener, filter, handback);
            return null;
        } else if (methodName.equals("removeNotificationListener")) {
            NotificationListener listener = (NotificationListener)(NotificationListener)args[0];
            switch (nargs) {
            case 1: 
                connection.removeNotificationListener(objectName, listener);
                return null;
            
            case 3: 
                NotificationFilter filter = (NotificationFilter)(NotificationFilter)args[1];
                Object handback = args[2];
                connection.removeNotificationListener(objectName, listener, filter, handback);
                return null;
            
            default: 
                final String msg = "Bad arg count to removeNotificationListener: " + nargs;
                throw new IllegalArgumentException(msg);
            
            }
        } else if (methodName.equals("getNotificationInfo")) {
            if (args != null) {
                throw new IllegalArgumentException("getNotificationInfo has args");
            }
            MBeanInfo info = connection.getMBeanInfo(objectName);
            return info.getNotifications();
        } else {
            throw new IllegalArgumentException("Bad method name: " + methodName);
        }
    }
    private final MBeanServerConnection connection;
    private final ObjectName objectName;
}
