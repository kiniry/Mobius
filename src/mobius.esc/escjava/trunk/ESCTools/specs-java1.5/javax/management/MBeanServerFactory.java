package javax.management;

import java.security.AccessController;
import java.security.Permission;
import java.security.PrivilegedAction;
import java.util.ArrayList;
import java.util.Iterator;
import javax.management.loading.ClassLoaderRepository;
import com.sun.jmx.defaults.ServiceName;
import com.sun.jmx.defaults.JmxProperties;
import com.sun.jmx.mbeanserver.GetPropertyAction;
import com.sun.jmx.trace.Trace;

public class MBeanServerFactory {
    
    private MBeanServerFactory() {
        
    }
    private static MBeanServerBuilder builder = null;
    
    public static void releaseMBeanServer(MBeanServer mbeanServer) {
        checkPermission("releaseMBeanServer");
        removeMBeanServer(mbeanServer);
    }
    
    public static MBeanServer createMBeanServer() {
        return createMBeanServer(null);
    }
    
    public static MBeanServer createMBeanServer(String domain) {
        checkPermission("createMBeanServer");
        final MBeanServer mBeanServer = newMBeanServer(domain);
        addMBeanServer(mBeanServer);
        return mBeanServer;
    }
    
    public static MBeanServer newMBeanServer() {
        return newMBeanServer(null);
    }
    
    public static MBeanServer newMBeanServer(String domain) {
        checkPermission("newMBeanServer");
        final MBeanServerBuilder mbsBuilder = getNewMBeanServerBuilder();
        synchronized (mbsBuilder) {
            final MBeanServerDelegate delegate = mbsBuilder.newMBeanServerDelegate();
            if (delegate == null) {
                final String msg = "MBeanServerBuilder.newMBeanServerDelegate() returned null";
                throw new JMRuntimeException(msg);
            }
            final MBeanServer mbeanServer = mbsBuilder.newMBeanServer(domain, null, delegate);
            if (mbeanServer == null) {
                final String msg = "MBeanServerBuilder.newMBeanServer() returned null";
                throw new JMRuntimeException(msg);
            }
            return mbeanServer;
        }
    }
    
    public static synchronized ArrayList findMBeanServer(String agentId) {
        checkPermission("findMBeanServer");
        if (agentId == null) return (ArrayList)(ArrayList)mBeanServerList.clone();
        ArrayList result = new ArrayList();
        for (Iterator i = mBeanServerList.iterator(); i.hasNext(); ) {
            MBeanServer mbs = (MBeanServer)(MBeanServer)i.next();
            String name = mBeanServerName(mbs);
            if (agentId.equals(name)) result.add(mbs);
        }
        return result;
    }
    
    public static ClassLoaderRepository getClassLoaderRepository(MBeanServer server) {
        return server.getClassLoaderRepository();
    }
    private static final ObjectName delegateName;
    static {
        ObjectName name;
        try {
            name = new ObjectName(ServiceName.DELEGATE);
        } catch (JMException e) {
            name = null;
            trace("<clinit>", "internal error creating delegate ObjectName: " + e);
        }
        delegateName = name;
    }
    
    private static String mBeanServerName(MBeanServer mbs) {
        try {
            return (String)(String)mbs.getAttribute(delegateName, "MBeanServerId");
        } catch (JMException e) {
            return null;
        }
    }
    
    private static void checkPermission(String action) throws SecurityException {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            Permission perm = new MBeanServerPermission(action);
            sm.checkPermission(perm);
        }
    }
    
    private static synchronized void addMBeanServer(MBeanServer mbs) {
        mBeanServerList.add(mbs);
    }
    
    private static synchronized void removeMBeanServer(MBeanServer mbs) {
        boolean removed = mBeanServerList.remove(mbs);
        if (!removed) {
            trace("removeMBeanServer", "MBeanServer was not in list!");
            throw new IllegalArgumentException("MBeanServer was not in list!");
        }
    }
    private static final ArrayList mBeanServerList = new ArrayList();
    
    private static Class loadBuilderClass(String builderClassName) throws ClassNotFoundException {
        final ClassLoader loader = Thread.currentThread().getContextClassLoader();
        if (loader != null) {
            return loader.loadClass(builderClassName);
        }
        return Class.forName(builderClassName);
    }
    
    private static MBeanServerBuilder newBuilder(Class builderClass) {
        try {
            final Object builder = builderClass.newInstance();
            return (MBeanServerBuilder)(MBeanServerBuilder)builder;
        } catch (RuntimeException x) {
            throw x;
        } catch (Exception x) {
            final String msg = "Failed to instantiate a MBeanServerBuilder from " + builderClass + ": " + x;
            throw new JMRuntimeException(msg, x);
        }
    }
    
    private static synchronized void checkMBeanServerBuilder() {
        try {
            PrivilegedAction act = new GetPropertyAction(JmxProperties.JMX_INITIAL_BUILDER);
            String builderClassName = (String)(String)AccessController.doPrivileged(act);
            try {
                final Class newBuilderClass;
                if (builderClassName == null || builderClassName.length() == 0) newBuilderClass = MBeanServerBuilder.class; else newBuilderClass = loadBuilderClass(builderClassName);
                if (builder != null) {
                    final Class builderClass = builder.getClass();
                    if (newBuilderClass == builderClass) return;
                }
                builder = newBuilder(newBuilderClass);
            } catch (ClassNotFoundException x) {
                final String msg = "Failed to load MBeanServerBuilder class " + builderClassName + ": " + x;
                throw new JMRuntimeException(msg, x);
            }
        } catch (RuntimeException x) {
            debug("checkMBeanServerBuilder", "Failed to instantiate MBeanServerBuilder: " + x + "\n\t\tCheck the value of the " + JmxProperties.JMX_INITIAL_BUILDER + " property.");
            throw x;
        }
    }
    
    private static synchronized MBeanServerBuilder getNewMBeanServerBuilder() {
        checkMBeanServerBuilder();
        return builder;
    }
    
    private static void trace(String method, String message) {
        if (Trace.isSelected(Trace.LEVEL_TRACE, Trace.INFO_MBEANSERVER)) {
            Trace.send(Trace.LEVEL_TRACE, Trace.INFO_MBEANSERVER, MBeanServerFactory.class.getName(), method, message);
        }
    }
    
    private static void debug(String method, String message) {
        if (Trace.isSelected(Trace.LEVEL_DEBUG, Trace.INFO_MBEANSERVER)) {
            Trace.send(Trace.LEVEL_DEBUG, Trace.INFO_MBEANSERVER, MBeanServerFactory.class.getName(), method, message);
        }
    }
    
    private static void error(String method, String message) {
        if (Trace.isSelected(Trace.LEVEL_ERROR, Trace.INFO_MBEANSERVER)) {
            Trace.send(Trace.LEVEL_ERROR, Trace.INFO_MBEANSERVER, MBeanServerFactory.class.getName(), method, message);
        }
    }
}
