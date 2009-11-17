package java.lang.management;

import javax.management.NotificationEmitter;
import javax.management.MBeanServer;
import javax.management.MBeanServerConnection;
import javax.management.MBeanServerPermission;
import javax.management.ObjectName;
import javax.management.InstanceNotFoundException;
import javax.management.MalformedObjectNameException;
import java.util.List;
import java.lang.reflect.Proxy;
import java.lang.reflect.InvocationHandler;
import java.security.AccessController;
import java.security.Permission;
import sun.management.PlatformMXBeanInvocationHandler;

public class ManagementFactory {
    
    private ManagementFactory() {
        
    }
    {
    }
    public static final String CLASS_LOADING_MXBEAN_NAME = "java.lang:type=ClassLoading";
    public static final String COMPILATION_MXBEAN_NAME = "java.lang:type=Compilation";
    public static final String MEMORY_MXBEAN_NAME = "java.lang:type=Memory";
    public static final String OPERATING_SYSTEM_MXBEAN_NAME = "java.lang:type=OperatingSystem";
    public static final String RUNTIME_MXBEAN_NAME = "java.lang:type=Runtime";
    public static final String THREAD_MXBEAN_NAME = "java.lang:type=Threading";
    public static final String GARBAGE_COLLECTOR_MXBEAN_DOMAIN_TYPE = "java.lang:type=GarbageCollector";
    public static final String MEMORY_MANAGER_MXBEAN_DOMAIN_TYPE = "java.lang:type=MemoryManager";
    public static final String MEMORY_POOL_MXBEAN_DOMAIN_TYPE = "java.lang:type=MemoryPool";
    
    public static ClassLoadingMXBean getClassLoadingMXBean() {
        return sun.management.ManagementFactory.getClassLoadingMXBean();
    }
    
    public static MemoryMXBean getMemoryMXBean() {
        return sun.management.ManagementFactory.getMemoryMXBean();
    }
    
    public static ThreadMXBean getThreadMXBean() {
        return sun.management.ManagementFactory.getThreadMXBean();
    }
    
    public static RuntimeMXBean getRuntimeMXBean() {
        return sun.management.ManagementFactory.getRuntimeMXBean();
    }
    
    public static CompilationMXBean getCompilationMXBean() {
        return sun.management.ManagementFactory.getCompilationMXBean();
    }
    
    public static OperatingSystemMXBean getOperatingSystemMXBean() {
        return sun.management.ManagementFactory.getOperatingSystemMXBean();
    }
    
    public static List getMemoryPoolMXBeans() {
        return sun.management.ManagementFactory.getMemoryPoolMXBeans();
    }
    
    public static List getMemoryManagerMXBeans() {
        return sun.management.ManagementFactory.getMemoryManagerMXBeans();
    }
    
    public static List getGarbageCollectorMXBeans() {
        return sun.management.ManagementFactory.getGarbageCollectorMXBeans();
    }
    private static MBeanServer platformMBeanServer;
    
    public static synchronized MBeanServer getPlatformMBeanServer() {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            Permission perm = new MBeanServerPermission("createMBeanServer");
            sm.checkPermission(perm);
        }
        if (platformMBeanServer == null) {
            platformMBeanServer = sun.management.ManagementFactory.createPlatformMBeanServer();
        }
        return platformMBeanServer;
    }
    
    public static Object newPlatformMXBeanProxy(MBeanServerConnection connection, String mxbeanName, Class mxbeanInterface) throws java.io.IOException {
        final Class interfaceClass = mxbeanInterface;
        final ClassLoader loader = (ClassLoader)(ClassLoader)AccessController.doPrivileged(new ManagementFactory$1(interfaceClass));
        if (loader != null) {
            throw new IllegalArgumentException(mxbeanName + " is not a platform MXBean");
        }
        try {
            final ObjectName objName = new ObjectName(mxbeanName);
            if (!connection.isInstanceOf(objName, interfaceClass.getName())) {
                throw new IllegalArgumentException(mxbeanName + " is not an instance of " + interfaceClass);
            }
            final Class[] interfaces;
            if (connection.isInstanceOf(objName, NOTIF_EMITTER)) {
                interfaces = new Class[]{interfaceClass, NotificationEmitter.class};
            } else {
                interfaces = new Class[]{interfaceClass};
            }
            InvocationHandler handler = new PlatformMXBeanInvocationHandler(connection, objName, interfaceClass);
            return (Object)Proxy.newProxyInstance(interfaceClass.getClassLoader(), interfaces, handler);
        } catch (InstanceNotFoundException e) {
            final IllegalArgumentException iae = new IllegalArgumentException(mxbeanName + " not found in the connection.");
            iae.initCause(e);
            throw iae;
        } catch (MalformedObjectNameException e) {
            final IllegalArgumentException iae = new IllegalArgumentException(mxbeanName + " is not a valid ObjectName format.");
            iae.initCause(e);
            throw iae;
        }
    }
    private static final String NOTIF_EMITTER = "javax.management.NotificationEmitter";
}
