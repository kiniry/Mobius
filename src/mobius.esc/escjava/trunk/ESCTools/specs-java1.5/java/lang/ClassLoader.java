package java.lang;

import java.io.InputStream;
import java.io.IOException;
import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.security.AccessController;
import java.security.AccessControlContext;
import java.security.CodeSource;
import java.security.PrivilegedActionException;
import java.security.PrivilegedExceptionAction;
import java.security.ProtectionDomain;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.Stack;
import java.util.Map;
import java.util.Vector;
import sun.misc.ClassFileTransformer;
import sun.misc.CompoundEnumeration;
import sun.misc.Resource;
import sun.misc.URLClassPath;
import sun.misc.VM;
import sun.reflect.Reflection;
import sun.security.util.SecurityConstants;

public abstract class ClassLoader {
    
    /*synthetic*/ static Stack access$100() {
        return nativeLibraryContext;
    }
    
    /*synthetic*/ static Vector access$000() {
        return loadedLibraryNames;
    }
    
    private static native void registerNatives();
    static {
        registerNatives();
    }
    private boolean initialized = false;
    private ClassLoader parent;
    private Hashtable package2certs = new Hashtable(11);
    java.security.cert.Certificate[] nocerts;
    private Vector classes = new Vector();
    private Set domains = new HashSet();
    
    void addClass(Class c) {
        classes.addElement(c);
    }
    private HashMap packages = new HashMap();
    
    protected ClassLoader(ClassLoader parent) {
        
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkCreateClassLoader();
        }
        this.parent = parent;
        initialized = true;
    }
    
    protected ClassLoader() {
        
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkCreateClassLoader();
        }
        this.parent = getSystemClassLoader();
        initialized = true;
    }
    
    public Class loadClass(String name) throws ClassNotFoundException {
        return loadClass(name, false);
    }
    
    protected synchronized Class loadClass(String name, boolean resolve) throws ClassNotFoundException {
        Class c = findLoadedClass(name);
        if (c == null) {
            try {
                if (parent != null) {
                    c = parent.loadClass(name, false);
                } else {
                    c = findBootstrapClass0(name);
                }
            } catch (ClassNotFoundException e) {
                c = findClass(name);
            }
        }
        if (resolve) {
            resolveClass(c);
        }
        return c;
    }
    
    private synchronized Class loadClassInternal(String name) throws ClassNotFoundException {
        return loadClass(name);
    }
    
    private void checkPackageAccess(Class cls, ProtectionDomain pd) {
        final SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            final String name = cls.getName();
            final int i = name.lastIndexOf('.');
            if (i != -1) {
                AccessController.doPrivileged(new ClassLoader$1(this, sm, name, i), new AccessControlContext(new ProtectionDomain[]{pd}));
            }
        }
        domains.add(pd);
    }
    
    protected Class findClass(String name) throws ClassNotFoundException {
        throw new ClassNotFoundException(name);
    }
    
    
    protected final Class defineClass(byte[] b, int off, int len) throws ClassFormatError {
        return defineClass(null, b, off, len, null);
    }
    
    protected final Class defineClass(String name, byte[] b, int off, int len) throws ClassFormatError {
        return defineClass(name, b, off, len, null);
    }
    
    private ProtectionDomain preDefineClass(String name, ProtectionDomain protectionDomain) {
        if (!checkName(name)) throw new NoClassDefFoundError("IllegalName: " + name);
        if ((name != null) && name.startsWith("java.")) {
            throw new SecurityException("Prohibited package name: " + name.substring(0, name.lastIndexOf('.')));
        }
        if (protectionDomain == null) {
            protectionDomain = getDefaultDomain();
        }
        if (name != null) checkCerts(name, protectionDomain.getCodeSource());
        return protectionDomain;
    }
    
    private String defineClassSourceLocation(ProtectionDomain protectionDomain) {
        CodeSource cs = protectionDomain.getCodeSource();
        String source = null;
        if (cs != null && cs.getLocation() != null) {
            source = cs.getLocation().toString();
        }
        return source;
    }
    
    private Class defineTransformedClass(String name, byte[] b, int off, int len, ProtectionDomain protectionDomain, ClassFormatError cfe, String source) throws ClassFormatError {
        Object[] transformers = ClassFileTransformer.getTransformers();
        Class c = null;
        for (int i = 0; transformers != null && i < transformers.length; i++) {
            try {
                byte[] tb = ((ClassFileTransformer)(ClassFileTransformer)transformers[i]).transform(b, off, len);
                c = defineClass1(name, tb, 0, tb.length, protectionDomain, source);
                break;
            } catch (ClassFormatError cfe2) {
            }
        }
        if (c == null) throw cfe;
        return c;
    }
    
    private void postDefineClass(Class c, ProtectionDomain protectionDomain) {
        if (protectionDomain.getCodeSource() != null) {
            java.security.cert.Certificate[] certs = protectionDomain.getCodeSource().getCertificates();
            if (certs != null) setSigners(c, certs);
        }
    }
    
    protected final Class defineClass(String name, byte[] b, int off, int len, ProtectionDomain protectionDomain) throws ClassFormatError {
        check();
        protectionDomain = preDefineClass(name, protectionDomain);
        Class c = null;
        String source = defineClassSourceLocation(protectionDomain);
        try {
            c = defineClass1(name, b, off, len, protectionDomain, source);
        } catch (ClassFormatError cfe) {
            c = defineTransformedClass(name, b, off, len, protectionDomain, cfe, source);
        }
        postDefineClass(c, protectionDomain);
        return c;
    }
    
    protected final Class defineClass(String name, java.nio.ByteBuffer b, ProtectionDomain protectionDomain) throws ClassFormatError {
        check();
        int len = b.remaining();
        if (!b.isDirect()) {
            if (b.hasArray()) {
                return defineClass(name, b.array(), b.position() + b.arrayOffset(), len, protectionDomain);
            } else {
                byte[] tb = new byte[len];
                b.get(tb);
                return defineClass(name, tb, 0, len, protectionDomain);
            }
        }
        protectionDomain = preDefineClass(name, protectionDomain);
        Class c = null;
        String source = defineClassSourceLocation(protectionDomain);
        try {
            c = defineClass2(name, b, b.position(), len, protectionDomain, source);
        } catch (ClassFormatError cfe) {
            byte[] tb = new byte[len];
            b.get(tb);
            c = defineTransformedClass(name, tb, 0, len, protectionDomain, cfe, source);
        }
        postDefineClass(c, protectionDomain);
        return c;
    }
    
    private native Class defineClass0(String name, byte[] b, int off, int len, ProtectionDomain pd);
    
    private native Class defineClass1(String name, byte[] b, int off, int len, ProtectionDomain pd, String source);
    
    private native Class defineClass2(String name, java.nio.ByteBuffer b, int off, int len, ProtectionDomain pd, String source);
    
    private boolean checkName(String name) {
        if ((name == null) || (name.length() == 0)) return true;
        if ((name.indexOf('/') != -1) || (!VM.allowArraySyntax() && (name.charAt(0) == '['))) return false;
        return true;
    }
    
    private synchronized void checkCerts(String name, CodeSource cs) {
        int i = name.lastIndexOf('.');
        String pname = (i == -1) ? "" : name.substring(0, i);
        java.security.cert.Certificate[] pcerts = (java.security.cert.Certificate[])(.java.security.cert.Certificate[])package2certs.get(pname);
        if (pcerts == null) {
            if (cs != null) {
                pcerts = cs.getCertificates();
            }
            if (pcerts == null) {
                if (nocerts == null) nocerts = new java.security.cert.Certificate[0];
                pcerts = nocerts;
            }
            package2certs.put(pname, pcerts);
        } else {
            java.security.cert.Certificate[] certs = null;
            if (cs != null) {
                certs = cs.getCertificates();
            }
            if (!compareCerts(pcerts, certs)) {
                throw new SecurityException("class \"" + name + "\"\'s signer information does not match signer information of other classes in the same package");
            }
        }
    }
    
    private boolean compareCerts(java.security.cert.Certificate[] pcerts, java.security.cert.Certificate[] certs) {
        if ((certs == null) || (certs.length == 0)) {
            return pcerts.length == 0;
        }
        if (certs.length != pcerts.length) return false;
        boolean match;
        for (int i = 0; i < certs.length; i++) {
            match = false;
            for (int j = 0; j < pcerts.length; j++) {
                if (certs[i].equals(pcerts[j])) {
                    match = true;
                    break;
                }
            }
            if (!match) return false;
        }
        for (int i = 0; i < pcerts.length; i++) {
            match = false;
            for (int j = 0; j < certs.length; j++) {
                if (pcerts[i].equals(certs[j])) {
                    match = true;
                    break;
                }
            }
            if (!match) return false;
        }
        return true;
    }
    
    protected final void resolveClass(Class c) {
        check();
        resolveClass0(c);
    }
    
    private native void resolveClass0(Class c);
    
    protected final Class findSystemClass(String name) throws ClassNotFoundException {
        check();
        ClassLoader system = getSystemClassLoader();
        if (system == null) {
            if (!checkName(name)) throw new ClassNotFoundException(name);
            return findBootstrapClass(name);
        }
        return system.loadClass(name);
    }
    
    private Class findBootstrapClass0(String name) throws ClassNotFoundException {
        check();
        if (!checkName(name)) throw new ClassNotFoundException(name);
        return findBootstrapClass(name);
    }
    
    private native Class findBootstrapClass(String name) throws ClassNotFoundException;
    
    private void check() {
        if (!initialized) {
            throw new SecurityException("ClassLoader object not initialized");
        }
    }
    
    protected final Class findLoadedClass(String name) {
        check();
        if (!checkName(name)) return null;
        return findLoadedClass0(name);
    }
    
    private final native Class findLoadedClass0(String name);
    
    protected final void setSigners(Class c, Object[] signers) {
        check();
        c.setSigners(signers);
    }
    
    public URL getResource(String name) {
        URL url;
        if (parent != null) {
            url = parent.getResource(name);
        } else {
            url = getBootstrapResource(name);
        }
        if (url == null) {
            url = findResource(name);
        }
        return url;
    }
    
    public Enumeration getResources(String name) throws IOException {
        Enumeration[] tmp = new Enumeration[2];
        if (parent != null) {
            tmp[0] = parent.getResources(name);
        } else {
            tmp[0] = getBootstrapResources(name);
        }
        tmp[1] = findResources(name);
        return new CompoundEnumeration(tmp);
    }
    
    protected URL findResource(String name) {
        return null;
    }
    
    protected Enumeration findResources(String name) throws IOException {
        return new CompoundEnumeration(new Enumeration[0]);
    }
    
    public static URL getSystemResource(String name) {
        ClassLoader system = getSystemClassLoader();
        if (system == null) {
            return getBootstrapResource(name);
        }
        return system.getResource(name);
    }
    
    public static Enumeration getSystemResources(String name) throws IOException {
        ClassLoader system = getSystemClassLoader();
        if (system == null) {
            return getBootstrapResources(name);
        }
        return system.getResources(name);
    }
    
    private static URL getBootstrapResource(String name) {
        URLClassPath ucp = getBootstrapClassPath();
        Resource res = ucp.getResource(name);
        return res != null ? res.getURL() : null;
    }
    
    private static Enumeration getBootstrapResources(String name) throws IOException {
        final Enumeration e = getBootstrapClassPath().getResources(name);
        return new ClassLoader$2(e);
    }
    
    static URLClassPath getBootstrapClassPath() {
        if (bootstrapClassPath == null) {
            bootstrapClassPath = sun.misc.Launcher.getBootstrapClassPath();
        }
        return bootstrapClassPath;
    }
    private static URLClassPath bootstrapClassPath;
    
    public InputStream getResourceAsStream(String name) {
        URL url = getResource(name);
        try {
            return url != null ? url.openStream() : null;
        } catch (IOException e) {
            return null;
        }
    }
    
    public static InputStream getSystemResourceAsStream(String name) {
        URL url = getSystemResource(name);
        try {
            return url != null ? url.openStream() : null;
        } catch (IOException e) {
            return null;
        }
    }
    
    public final ClassLoader getParent() {
        if (parent == null) return null;
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            ClassLoader ccl = getCallerClassLoader();
            if (ccl != null && !isAncestor(ccl)) {
                sm.checkPermission(SecurityConstants.GET_CLASSLOADER_PERMISSION);
            }
        }
        return parent;
    }
    
    public static ClassLoader getSystemClassLoader() {
        initSystemClassLoader();
        if (scl == null) {
            return null;
        }
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            ClassLoader ccl = getCallerClassLoader();
            if (ccl != null && ccl != scl && !scl.isAncestor(ccl)) {
                sm.checkPermission(SecurityConstants.GET_CLASSLOADER_PERMISSION);
            }
        }
        return scl;
    }
    
    private static synchronized void initSystemClassLoader() {
        if (!sclSet) {
            if (scl != null) throw new IllegalStateException("recursive invocation");
            sun.misc.Launcher l = sun.misc.Launcher.getLauncher();
            if (l != null) {
                Throwable oops = null;
                scl = l.getClassLoader();
                try {
                    PrivilegedExceptionAction a;
                    a = new SystemClassLoaderAction(scl);
                    scl = (ClassLoader)(ClassLoader)AccessController.doPrivileged(a);
                } catch (PrivilegedActionException pae) {
                    oops = pae.getCause();
                    if (oops instanceof InvocationTargetException) {
                        oops = oops.getCause();
                    }
                }
                if (oops != null) {
                    if (oops instanceof Error) {
                        throw (Error)(Error)oops;
                    } else {
                        throw new Error(oops);
                    }
                }
            }
            sclSet = true;
        }
    }
    
    boolean isAncestor(ClassLoader cl) {
        ClassLoader acl = this;
        do {
            acl = acl.parent;
            if (cl == acl) {
                return true;
            }
        }         while (acl != null);
        return false;
    }
    
    static ClassLoader getCallerClassLoader() {
        Class caller = Reflection.getCallerClass(3);
        if (caller == null) {
            return null;
        }
        return caller.getClassLoader0();
    }
    private static ClassLoader scl;
    private static boolean sclSet;
    
    protected Package definePackage(String name, String specTitle, String specVersion, String specVendor, String implTitle, String implVersion, String implVendor, URL sealBase) throws IllegalArgumentException {
        synchronized (packages) {
            Package pkg = getPackage(name);
            if (pkg != null) {
                throw new IllegalArgumentException(name);
            }
            pkg = new Package(name, specTitle, specVersion, specVendor, implTitle, implVersion, implVendor, sealBase, this);
            packages.put(name, pkg);
            return pkg;
        }
    }
    
    protected Package getPackage(String name) {
        synchronized (packages) {
            Package pkg = (Package)(Package)packages.get(name);
            if (pkg == null) {
                if (parent != null) {
                    pkg = parent.getPackage(name);
                } else {
                    pkg = Package.getSystemPackage(name);
                }
                if (pkg != null) {
                    packages.put(name, pkg);
                }
            }
            return pkg;
        }
    }
    
    protected Package[] getPackages() {
        Map map;
        synchronized (packages) {
            map = (Map)(Map)packages.clone();
        }
        Package[] pkgs;
        if (parent != null) {
            pkgs = parent.getPackages();
        } else {
            pkgs = Package.getSystemPackages();
        }
        if (pkgs != null) {
            for (int i = 0; i < pkgs.length; i++) {
                String pkgName = pkgs[i].getName();
                if (map.get(pkgName) == null) {
                    map.put(pkgName, pkgs[i]);
                }
            }
        }
        return (Package[])(Package[])map.values().toArray(new Package[map.size()]);
    }
    
    protected String findLibrary(String libname) {
        return null;
    }
    {
    }
    private ProtectionDomain defaultDomain = null;
    
    private synchronized ProtectionDomain getDefaultDomain() {
        if (defaultDomain == null) {
            CodeSource cs = new CodeSource(null, (java.security.cert.Certificate[])null);
            defaultDomain = new ProtectionDomain(cs, null, this, null);
        }
        return defaultDomain;
    }
    private static Vector loadedLibraryNames = new Vector();
    private static Vector systemNativeLibraries = new Vector();
    private Vector nativeLibraries = new Vector();
    private static Stack nativeLibraryContext = new Stack();
    private static String[] usr_paths;
    private static String[] sys_paths;
    
    private static String[] initializePath(String propname) {
        String ldpath = System.getProperty(propname, "");
        String ps = File.pathSeparator;
        int ldlen = ldpath.length();
        int i;
        int j;
        int n;
        i = ldpath.indexOf(ps);
        n = 0;
        while (i >= 0) {
            n++;
            i = ldpath.indexOf(ps, i + 1);
        }
        String[] paths = new String[n + 1];
        n = i = 0;
        j = ldpath.indexOf(ps);
        while (j >= 0) {
            if (j - i > 0) {
                paths[n++] = ldpath.substring(i, j);
            } else if (j - i == 0) {
                paths[n++] = ".";
            }
            i = j + 1;
            j = ldpath.indexOf(ps, i);
        }
        paths[n] = ldpath.substring(i, ldlen);
        return paths;
    }
    
    static void loadLibrary(Class fromClass, String name, boolean isAbsolute) {
        ClassLoader loader = (fromClass == null) ? null : fromClass.getClassLoader();
        if (sys_paths == null) {
            usr_paths = initializePath("java.library.path");
            sys_paths = initializePath("sun.boot.library.path");
        }
        if (isAbsolute) {
            if (loadLibrary0(fromClass, new File(name))) {
                return;
            }
            throw new UnsatisfiedLinkError("Can\'t load library: " + name);
        }
        if (loader != null) {
            String libfilename = loader.findLibrary(name);
            if (libfilename != null) {
                File libfile = new File(libfilename);
                if (!libfile.isAbsolute()) {
                    throw new UnsatisfiedLinkError("ClassLoader.findLibrary failed to return an absolute path: " + libfilename);
                }
                if (loadLibrary0(fromClass, libfile)) {
                    return;
                }
                throw new UnsatisfiedLinkError("Can\'t load " + libfilename);
            }
        }
        for (int i = 0; i < sys_paths.length; i++) {
            File libfile = new File(sys_paths[i], System.mapLibraryName(name));
            if (loadLibrary0(fromClass, libfile)) {
                return;
            }
        }
        if (loader != null) {
            for (int i = 0; i < usr_paths.length; i++) {
                File libfile = new File(usr_paths[i], System.mapLibraryName(name));
                if (loadLibrary0(fromClass, libfile)) {
                    return;
                }
            }
        }
        throw new UnsatisfiedLinkError("no " + name + " in java.library.path");
    }
    
    private static boolean loadLibrary0(Class fromClass, final File file) {
        Boolean exists = (Boolean)(Boolean)AccessController.doPrivileged(new ClassLoader$3(file));
        if (!exists.booleanValue()) {
            return false;
        }
        String name;
        try {
            name = file.getCanonicalPath();
        } catch (IOException e) {
            return false;
        }
        ClassLoader loader = (fromClass == null) ? null : fromClass.getClassLoader();
        Vector libs = loader != null ? loader.nativeLibraries : systemNativeLibraries;
        synchronized (libs) {
            int size = libs.size();
            for (int i = 0; i < size; i++) {
                ClassLoader$NativeLibrary lib = (ClassLoader$NativeLibrary)(ClassLoader$NativeLibrary)libs.elementAt(i);
                if (name.equals(lib.name)) {
                    return true;
                }
            }
            synchronized (loadedLibraryNames) {
                if (loadedLibraryNames.contains(name)) {
                    throw new UnsatisfiedLinkError("Native Library " + name + " already loaded in another classloader");
                }
                int n = nativeLibraryContext.size();
                for (int i = 0; i < n; i++) {
                    ClassLoader$NativeLibrary lib = (ClassLoader$NativeLibrary)(ClassLoader$NativeLibrary)nativeLibraryContext.elementAt(i);
                    if (name.equals(lib.name)) {
                        if (loader == ClassLoader.NativeLibrary.access$200(lib).getClassLoader()) {
                            return true;
                        } else {
                            throw new UnsatisfiedLinkError("Native Library " + name + " is being loaded in another classloader");
                        }
                    }
                }
                ClassLoader$NativeLibrary lib = new ClassLoader$NativeLibrary(fromClass, name);
                nativeLibraryContext.push(lib);
                try {
                    lib.load(name);
                } finally {
                    nativeLibraryContext.pop();
                }
                if (lib.handle != 0) {
                    loadedLibraryNames.addElement(name);
                    libs.addElement(lib);
                    return true;
                }
                return false;
            }
        }
    }
    
    static long findNative(ClassLoader loader, String name) {
        Vector libs = loader != null ? loader.nativeLibraries : systemNativeLibraries;
        synchronized (libs) {
            int size = libs.size();
            for (int i = 0; i < size; i++) {
                ClassLoader$NativeLibrary lib = (ClassLoader$NativeLibrary)(ClassLoader$NativeLibrary)libs.elementAt(i);
                long entry = lib.find(name);
                if (entry != 0) return entry;
            }
        }
        return 0;
    }
    private boolean defaultAssertionStatus = false;
    private Map packageAssertionStatus = null;
    Map classAssertionStatus = null;
    
    public synchronized void setDefaultAssertionStatus(boolean enabled) {
        if (classAssertionStatus == null) initializeJavaAssertionMaps();
        defaultAssertionStatus = enabled;
    }
    
    public synchronized void setPackageAssertionStatus(String packageName, boolean enabled) {
        if (packageAssertionStatus == null) initializeJavaAssertionMaps();
        packageAssertionStatus.put(packageName, Boolean.valueOf(enabled));
    }
    
    public synchronized void setClassAssertionStatus(String className, boolean enabled) {
        if (classAssertionStatus == null) initializeJavaAssertionMaps();
        classAssertionStatus.put(className, Boolean.valueOf(enabled));
    }
    
    public synchronized void clearAssertionStatus() {
        classAssertionStatus = new HashMap();
        packageAssertionStatus = new HashMap();
        defaultAssertionStatus = false;
    }
    
    synchronized boolean desiredAssertionStatus(String className) {
        Boolean result;
        result = (Boolean)(Boolean)classAssertionStatus.get(className);
        if (result != null) return result.booleanValue();
        int dotIndex = className.lastIndexOf(".");
        if (dotIndex < 0) {
            result = (Boolean)(Boolean)packageAssertionStatus.get(null);
            if (result != null) return result.booleanValue();
        }
        while (dotIndex > 0) {
            className = className.substring(0, dotIndex);
            result = (Boolean)(Boolean)packageAssertionStatus.get(className);
            if (result != null) return result.booleanValue();
            dotIndex = className.lastIndexOf(".", dotIndex - 1);
        }
        return defaultAssertionStatus;
    }
    
    private void initializeJavaAssertionMaps() {
        classAssertionStatus = new HashMap();
        packageAssertionStatus = new HashMap();
        AssertionStatusDirectives directives = retrieveDirectives();
        for (int i = 0; i < directives.classes.length; i++) classAssertionStatus.put(directives.classes[i], Boolean.valueOf(directives.classEnabled[i]));
        for (int i = 0; i < directives.packages.length; i++) packageAssertionStatus.put(directives.packages[i], Boolean.valueOf(directives.packageEnabled[i]));
        defaultAssertionStatus = directives.deflt;
    }
    
    private static native AssertionStatusDirectives retrieveDirectives();
}
