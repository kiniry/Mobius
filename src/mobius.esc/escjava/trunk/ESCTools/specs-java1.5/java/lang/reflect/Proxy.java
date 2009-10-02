package java.lang.reflect;

import java.lang.ref.Reference;
import java.lang.ref.WeakReference;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;
import sun.misc.ProxyGenerator;

public class Proxy implements java.io.Serializable {
    private static final long serialVersionUID = -2222568056686623797L;
    private static final String proxyClassNamePrefix = "$Proxy";
    private static final Class[] constructorParams = {InvocationHandler.class};
    private static Map loaderToCache = new WeakHashMap();
    private static Object pendingGenerationMarker = new Object();
    private static long nextUniqueNumber = 0;
    private static Object nextUniqueNumberLock = new Object();
    private static Map proxyClasses = Collections.synchronizedMap(new WeakHashMap());
    protected InvocationHandler h;
    
    private Proxy() {
        
    }
    
    protected Proxy(InvocationHandler h) {
        
        this.h = h;
    }
    
    public static Class getProxyClass(ClassLoader loader, Class... interfaces) throws IllegalArgumentException {
        if (interfaces.length > 65535) {
            throw new IllegalArgumentException("interface limit exceeded");
        }
        Class proxyClass = null;
        String[] interfaceNames = new String[interfaces.length];
        Set interfaceSet = new HashSet();
        for (int i = 0; i < interfaces.length; i++) {
            String interfaceName = interfaces[i].getName();
            Class interfaceClass = null;
            try {
                interfaceClass = Class.forName(interfaceName, false, loader);
            } catch (ClassNotFoundException e) {
            }
            if (interfaceClass != interfaces[i]) {
                throw new IllegalArgumentException(interfaces[i] + " is not visible from class loader");
            }
            if (!interfaceClass.isInterface()) {
                throw new IllegalArgumentException(interfaceClass.getName() + " is not an interface");
            }
            if (interfaceSet.contains(interfaceClass)) {
                throw new IllegalArgumentException("repeated interface: " + interfaceClass.getName());
            }
            interfaceSet.add(interfaceClass);
            interfaceNames[i] = interfaceName;
        }
        Object key = Arrays.asList(interfaceNames);
        Map cache;
        synchronized (loaderToCache) {
            cache = (Map)(Map)loaderToCache.get(loader);
            if (cache == null) {
                cache = new HashMap();
                loaderToCache.put(loader, cache);
            }
        }
        synchronized (cache) {
            do {
                Object value = cache.get(key);
                if (value instanceof Reference) {
                    proxyClass = (Class)(Class)((Reference)(Reference)value).get();
                }
                if (proxyClass != null) {
                    return proxyClass;
                } else if (value == pendingGenerationMarker) {
                    try {
                        cache.wait();
                    } catch (InterruptedException e) {
                    }
                    continue;
                } else {
                    cache.put(key, pendingGenerationMarker);
                    break;
                }
            }             while (true);
        }
        try {
            String proxyPkg = null;
            for (int i = 0; i < interfaces.length; i++) {
                int flags = interfaces[i].getModifiers();
                if (!Modifier.isPublic(flags)) {
                    String name = interfaces[i].getName();
                    int n = name.lastIndexOf('.');
                    String pkg = ((n == -1) ? "" : name.substring(0, n + 1));
                    if (proxyPkg == null) {
                        proxyPkg = pkg;
                    } else if (!pkg.equals(proxyPkg)) {
                        throw new IllegalArgumentException("non-public interfaces from different packages");
                    }
                }
            }
            if (proxyPkg == null) {
                proxyPkg = "";
            }
            {
                long num;
                synchronized (nextUniqueNumberLock) {
                    num = nextUniqueNumber++;
                }
                String proxyName = proxyPkg + proxyClassNamePrefix + num;
                byte[] proxyClassFile = ProxyGenerator.generateProxyClass(proxyName, interfaces);
                try {
                    proxyClass = defineClass0(loader, proxyName, proxyClassFile, 0, proxyClassFile.length);
                } catch (ClassFormatError e) {
                    throw new IllegalArgumentException(e.toString());
                }
            }
            proxyClasses.put(proxyClass, null);
        } finally {
            synchronized (cache) {
                if (proxyClass != null) {
                    cache.put(key, new WeakReference(proxyClass));
                } else {
                    cache.remove(key);
                }
                cache.notifyAll();
            }
        }
        return proxyClass;
    }
    
    public static Object newProxyInstance(ClassLoader loader, Class[] interfaces, InvocationHandler h) throws IllegalArgumentException {
        if (h == null) {
            throw new NullPointerException();
        }
        Class cl = getProxyClass(loader, interfaces);
        try {
            Constructor cons = cl.getConstructor(constructorParams);
            return (Object)cons.newInstance(new Object[]{h});
        } catch (NoSuchMethodException e) {
            throw new InternalError(e.toString());
        } catch (IllegalAccessException e) {
            throw new InternalError(e.toString());
        } catch (InstantiationException e) {
            throw new InternalError(e.toString());
        } catch (InvocationTargetException e) {
            throw new InternalError(e.toString());
        }
    }
    
    public static boolean isProxyClass(Class cl) {
        if (cl == null) {
            throw new NullPointerException();
        }
        return proxyClasses.containsKey(cl);
    }
    
    public static InvocationHandler getInvocationHandler(Object proxy) throws IllegalArgumentException {
        if (!isProxyClass(proxy.getClass())) {
            throw new IllegalArgumentException("not a proxy instance");
        }
        Proxy p = (Proxy)(Proxy)proxy;
        return p.h;
    }
    
    private static native Class defineClass0(ClassLoader loader, String name, byte[] b, int off, int len);
}
