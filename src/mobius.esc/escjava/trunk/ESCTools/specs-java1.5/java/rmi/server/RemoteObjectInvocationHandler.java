package java.rmi.server;

import java.io.InvalidObjectException;
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;
import java.rmi.Remote;
import java.rmi.UnexpectedException;
import java.util.Map;

public class RemoteObjectInvocationHandler extends RemoteObject implements InvocationHandler {
    private static final long serialVersionUID = 2L;
    private static final RemoteObjectInvocationHandler$MethodToHash_Maps methodToHash_Maps = new RemoteObjectInvocationHandler$MethodToHash_Maps();
    
    public RemoteObjectInvocationHandler(RemoteRef ref) {
        super(ref);
        if (ref == null) {
            throw new NullPointerException();
        }
    }
    
    public Object invoke(Object proxy, Method method, Object[] args) throws Throwable {
        if (method.getDeclaringClass() == Object.class) {
            return invokeObjectMethod(proxy, method, args);
        } else {
            return invokeRemoteMethod(proxy, method, args);
        }
    }
    
    private Object invokeObjectMethod(Object proxy, Method method, Object[] args) {
        String name = method.getName();
        if (name.equals("hashCode")) {
            return new Integer(hashCode());
        } else if (name.equals("equals")) {
            Object obj = args[0];
            boolean b = proxy == obj || (obj != null && Proxy.isProxyClass(obj.getClass()) && equals(Proxy.getInvocationHandler(obj)));
            return Boolean.valueOf(b);
        } else if (name.equals("toString")) {
            return proxyToString(proxy);
        } else {
            throw new IllegalArgumentException("unexpected Object method: " + method);
        }
    }
    
    private Object invokeRemoteMethod(Object proxy, Method method, Object[] args) throws Exception {
        try {
            if (!(proxy instanceof Remote)) {
                throw new IllegalArgumentException("proxy not Remote instance");
            }
            return ref.invoke((Remote)(Remote)proxy, method, args, getMethodHash(method));
        } catch (Exception e) {
            if (!(e instanceof RuntimeException)) {
                Class cl = proxy.getClass();
                try {
                    method = cl.getMethod(method.getName(), method.getParameterTypes());
                } catch (NoSuchMethodException nsme) {
                    throw (IllegalArgumentException)(IllegalArgumentException)new IllegalArgumentException().initCause(nsme);
                }
                Class[] exTypes = method.getExceptionTypes();
                Class thrownType = e.getClass();
                for (int i = 0; i < exTypes.length; i++) {
                    if (exTypes[i].isAssignableFrom(thrownType)) {
                        throw e;
                    }
                }
                e = new UnexpectedException("unexpected exception", e);
            }
            throw e;
        }
    }
    
    private String proxyToString(Object proxy) {
        Class[] interfaces = proxy.getClass().getInterfaces();
        if (interfaces.length == 0) {
            return "Proxy[" + this + "]";
        }
        String iface = interfaces[0].getName();
        if (iface.equals("java.rmi.Remote") && interfaces.length > 1) {
            iface = interfaces[1].getName();
        }
        int dot = iface.lastIndexOf('.');
        if (dot >= 0) {
            iface = iface.substring(dot + 1);
        }
        return "Proxy[" + iface + "," + this + "]";
    }
    
    private void readObjectNoData() throws InvalidObjectException {
        throw new InvalidObjectException("no data in stream; class: " + this.getClass().getName());
    }
    
    private static long getMethodHash(Method method) {
        Map map = methodToHash_Maps.getMap(method.getDeclaringClass());
        Long hash = (Long)(Long)map.get(method);
        return hash.longValue();
    }
    {
    }
}
