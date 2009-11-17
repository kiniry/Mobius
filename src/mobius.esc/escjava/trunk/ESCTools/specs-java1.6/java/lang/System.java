package java.lang;

import java.io.*;
import java.util.Properties;
import java.util.PropertyPermission;
import java.security.AccessController;
import java.nio.channels.Channel;
import java.nio.channels.spi.SelectorProvider;
import sun.net.InetAddressCachePolicy;
import sun.reflect.Reflection;
import sun.security.util.SecurityConstants;

public final class System {
    
    private static native void registerNatives();
    static {
        registerNatives();
    }
    
    private System() {
        
    }
    public static final InputStream in = nullInputStream();
    public static final PrintStream out = nullPrintStream();
    public static final PrintStream err = nullPrintStream();
    private static SecurityManager security = null;
    
    public static void setIn(InputStream in) {
        checkIO();
        setIn0(in);
    }
    
    public static void setOut(PrintStream out) {
        checkIO();
        setOut0(out);
    }
    
    public static void setErr(PrintStream err) {
        checkIO();
        setErr0(err);
    }
    
    public static Channel inheritedChannel() throws IOException {
        return SelectorProvider.provider().inheritedChannel();
    }
    
    private static void checkIO() {
        if (security != null) security.checkPermission(new RuntimePermission("setIO"));
    }
    
    private static native void setIn0(InputStream in);
    
    private static native void setOut0(PrintStream out);
    
    private static native void setErr0(PrintStream err);
    
    public static void setSecurityManager(final SecurityManager s) {
        try {
            s.checkPackageAccess("java.lang");
        } catch (Exception e) {
        }
        setSecurityManager0(s);
    }
    
    private static synchronized void setSecurityManager0(final SecurityManager s) {
        if (security != null) {
            security.checkPermission(new RuntimePermission("setSecurityManager"));
        }
        if ((s != null) && (s.getClass().getClassLoader() != null)) {
            AccessController.doPrivileged(new System$1(s));
        }
        security = s;
        InetAddressCachePolicy.setIfNotSet(InetAddressCachePolicy.FOREVER);
    }
    
    public static SecurityManager getSecurityManager() {
        return security;
    }
    
    public static native long currentTimeMillis();
    
    public static native long nanoTime();
    
    public static native void arraycopy(Object src, int srcPos, Object dest, int destPos, int length);
    
    public static native int identityHashCode(Object x);
    private static Properties props;
    
    private static native Properties initProperties(Properties props);
    
    public static Properties getProperties() {
        if (security != null) {
            security.checkPropertiesAccess();
        }
        return props;
    }
    
    public static void setProperties(Properties props) {
        if (security != null) {
            security.checkPropertiesAccess();
        }
        if (props == null) {
            props = new Properties();
            initProperties(props);
        }
        System.props = props;
    }
    
    public static String getProperty(String key) {
        checkKey(key);
        if (security != null) {
            security.checkPropertyAccess(key);
        }
        return props.getProperty(key);
    }
    
    public static String getProperty(String key, String def) {
        checkKey(key);
        if (security != null) {
            security.checkPropertyAccess(key);
        }
        return props.getProperty(key, def);
    }
    
    public static String setProperty(String key, String value) {
        checkKey(key);
        if (security != null) security.checkPermission(new PropertyPermission(key, SecurityConstants.PROPERTY_WRITE_ACTION));
        return (String)(String)props.setProperty(key, value);
    }
    
    public static String clearProperty(String key) {
        checkKey(key);
        if (security != null) security.checkPermission(new PropertyPermission(key, "write"));
        return (String)(String)props.remove(key);
    }
    
    private static void checkKey(String key) {
        if (key == null) {
            throw new NullPointerException("key can\'t be null");
        }
        if (key.equals("")) {
            throw new IllegalArgumentException("key can\'t be empty");
        }
    }
    
    public static String getenv(String name) {
        if (security != null) security.checkPermission(new RuntimePermission("getenv." + name));
        return ProcessEnvironment.getenv(name);
    }
    
    public static java.util.Map getenv() {
        if (security != null) security.checkPermission(new RuntimePermission("getenv.*"));
        return ProcessEnvironment.getenv();
    }
    
    public static void exit(int status) {
        Runtime.getRuntime().exit(status);
    }
    
    public static void gc() {
        Runtime.getRuntime().gc();
    }
    
    public static void runFinalization() {
        Runtime.getRuntime().runFinalization();
    }
    
    
    public static void runFinalizersOnExit(boolean value) {
        Runtime.getRuntime().runFinalizersOnExit(value);
    }
    
    public static void load(String filename) {
        Runtime.getRuntime().load0(getCallerClass(), filename);
    }
    
    public static void loadLibrary(String libname) {
        Runtime.getRuntime().loadLibrary0(getCallerClass(), libname);
    }
    
    public static native String mapLibraryName(String libname);
    
    private static InputStream nullInputStream() throws NullPointerException {
        if (currentTimeMillis() > 0) return null;
        throw new NullPointerException();
    }
    
    private static PrintStream nullPrintStream() throws NullPointerException {
        if (currentTimeMillis() > 0) return null;
        throw new NullPointerException();
    }
    
    private static void initializeSystemClass() {
        props = new Properties();
        initProperties(props);
        sun.misc.Version.init();
        FileInputStream fdIn = new FileInputStream(FileDescriptor.in);
        FileOutputStream fdOut = new FileOutputStream(FileDescriptor.out);
        FileOutputStream fdErr = new FileOutputStream(FileDescriptor.err);
        setIn0(new BufferedInputStream(fdIn));
        setOut0(new PrintStream(new BufferedOutputStream(fdOut, 128), true));
        setErr0(new PrintStream(new BufferedOutputStream(fdErr, 128), true));
        loadLibrary("zip");
        Terminator.setup();
        sun.misc.VM.maxDirectMemory();
        sun.misc.VM.allowArraySyntax();
        sun.misc.VM.booted();
        Thread current = Thread.currentThread();
        current.getThreadGroup().add(current);
        sun.misc.SharedSecrets.setJavaLangAccess(new System$2());
    }
    
    static Class getCallerClass() {
        return Reflection.getCallerClass(3);
    }
}
