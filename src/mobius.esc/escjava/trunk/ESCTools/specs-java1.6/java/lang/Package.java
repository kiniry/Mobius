package java.lang;

import java.io.FileInputStream;
import java.io.IOException;
import java.net.URL;
import java.security.AccessController;
import java.util.jar.JarInputStream;
import java.util.jar.Manifest;
import java.util.jar.Attributes;
import java.util.jar.Attributes.Name;
import java.util.Map;
import java.util.HashMap;
import java.lang.annotation.Annotation;

public class Package implements java.lang.reflect.AnnotatedElement {
    
    /*synthetic*/ static Map access$400() {
        return pkgs;
    }
    
    /*synthetic*/ Package(String x0, Manifest x1, URL x2, ClassLoader x3, java.lang.Package$1 x4) {
        this(x0, x1, x2, x3);
    }
    
    /*synthetic*/ static Map access$200() {
        return mans;
    }
    
    /*synthetic*/ static Manifest access$100(String x0) {
        return loadManifest(x0);
    }
    
    /*synthetic*/ static Map access$000() {
        return urls;
    }
    
    public String getName() {
        return pkgName;
    }
    
    public String getSpecificationTitle() {
        return specTitle;
    }
    
    public String getSpecificationVersion() {
        return specVersion;
    }
    
    public String getSpecificationVendor() {
        return specVendor;
    }
    
    public String getImplementationTitle() {
        return implTitle;
    }
    
    public String getImplementationVersion() {
        return implVersion;
    }
    
    public String getImplementationVendor() {
        return implVendor;
    }
    
    public boolean isSealed() {
        return sealBase != null;
    }
    
    public boolean isSealed(URL url) {
        return url.equals(sealBase);
    }
    
    public boolean isCompatibleWith(String desired) throws NumberFormatException {
        if (specVersion == null || specVersion.length() < 1) {
            throw new NumberFormatException("Empty version string");
        }
        String[] sa = specVersion.split("\\.", -1);
        int[] si = new int[sa.length];
        for (int i = 0; i < sa.length; i++) {
            si[i] = Integer.parseInt(sa[i]);
            if (si[i] < 0) throw NumberFormatException.forInputString("" + si[i]);
        }
        String[] da = desired.split("\\.", -1);
        int[] di = new int[da.length];
        for (int i = 0; i < da.length; i++) {
            di[i] = Integer.parseInt(da[i]);
            if (di[i] < 0) throw NumberFormatException.forInputString("" + di[i]);
        }
        int len = Math.max(di.length, si.length);
        for (int i = 0; i < len; i++) {
            int d = (i < di.length ? di[i] : 0);
            int s = (i < si.length ? si[i] : 0);
            if (s < d) return false;
            if (s > d) return true;
        }
        return true;
    }
    
    public static Package getPackage(String name) {
        ClassLoader l = ClassLoader.getCallerClassLoader();
        if (l != null) {
            return l.getPackage(name);
        } else {
            return getSystemPackage(name);
        }
    }
    
    public static Package[] getPackages() {
        ClassLoader l = ClassLoader.getCallerClassLoader();
        if (l != null) {
            return l.getPackages();
        } else {
            return getSystemPackages();
        }
    }
    
    static Package getPackage(Class c) {
        String name = c.getName();
        int i = name.lastIndexOf('.');
        if (i != -1) {
            name = name.substring(0, i);
            ClassLoader cl = c.getClassLoader();
            if (cl != null) {
                return cl.getPackage(name);
            } else {
                return getSystemPackage(name);
            }
        } else {
            return null;
        }
    }
    
    public int hashCode() {
        return pkgName.hashCode();
    }
    
    public String toString() {
        String spec = specTitle;
        String ver = specVersion;
        if (spec != null && spec.length() > 0) spec = ", " + spec; else spec = "";
        if (ver != null && ver.length() > 0) ver = ", version " + ver; else ver = "";
        return "package " + pkgName + spec + ver;
    }
    
    private Class getPackageInfo() {
        if (packageInfo == null) {
            try {
                packageInfo = Class.forName(pkgName + ".package-info", false, loader);
            } catch (ClassNotFoundException ex) {
                {
                }
                packageInfo = PackageInfoProxy.class;
            }
        }
        return packageInfo;
    }
    
    public Annotation getAnnotation(Class annotationClass) {
        return getPackageInfo().getAnnotation(annotationClass);
    }
    
    public boolean isAnnotationPresent(Class annotationClass) {
        return getPackageInfo().isAnnotationPresent(annotationClass);
    }
    
    public Annotation[] getAnnotations() {
        return getPackageInfo().getAnnotations();
    }
    
    public Annotation[] getDeclaredAnnotations() {
        return getPackageInfo().getDeclaredAnnotations();
    }
    
    Package(String name, String spectitle, String specversion, String specvendor, String impltitle, String implversion, String implvendor, URL sealbase, ClassLoader loader) {
        
        pkgName = name;
        implTitle = impltitle;
        implVersion = implversion;
        implVendor = implvendor;
        specTitle = spectitle;
        specVersion = specversion;
        specVendor = specvendor;
        sealBase = sealbase;
        this.loader = loader;
    }
    
    private Package(String name, Manifest man, URL url, ClassLoader loader) {
        
        String path = name.replace('.', '/').concat("/");
        String sealed = null;
        String specTitle = null;
        String specVersion = null;
        String specVendor = null;
        String implTitle = null;
        String implVersion = null;
        String implVendor = null;
        URL sealBase = null;
        Attributes attr = man.getAttributes(path);
        if (attr != null) {
            specTitle = attr.getValue(Attributes$Name.SPECIFICATION_TITLE);
            specVersion = attr.getValue(Attributes$Name.SPECIFICATION_VERSION);
            specVendor = attr.getValue(Attributes$Name.SPECIFICATION_VENDOR);
            implTitle = attr.getValue(Attributes$Name.IMPLEMENTATION_TITLE);
            implVersion = attr.getValue(Attributes$Name.IMPLEMENTATION_VERSION);
            implVendor = attr.getValue(Attributes$Name.IMPLEMENTATION_VENDOR);
            sealed = attr.getValue(Attributes$Name.SEALED);
        }
        attr = man.getMainAttributes();
        if (attr != null) {
            if (specTitle == null) {
                specTitle = attr.getValue(Attributes$Name.SPECIFICATION_TITLE);
            }
            if (specVersion == null) {
                specVersion = attr.getValue(Attributes$Name.SPECIFICATION_VERSION);
            }
            if (specVendor == null) {
                specVendor = attr.getValue(Attributes$Name.SPECIFICATION_VENDOR);
            }
            if (implTitle == null) {
                implTitle = attr.getValue(Attributes$Name.IMPLEMENTATION_TITLE);
            }
            if (implVersion == null) {
                implVersion = attr.getValue(Attributes$Name.IMPLEMENTATION_VERSION);
            }
            if (implVendor == null) {
                implVendor = attr.getValue(Attributes$Name.IMPLEMENTATION_VENDOR);
            }
            if (sealed == null) {
                sealed = attr.getValue(Attributes$Name.SEALED);
            }
        }
        if ("true".equalsIgnoreCase(sealed)) {
            sealBase = url;
        }
        pkgName = name;
        this.specTitle = specTitle;
        this.specVersion = specVersion;
        this.specVendor = specVendor;
        this.implTitle = implTitle;
        this.implVersion = implVersion;
        this.implVendor = implVendor;
        this.sealBase = sealBase;
        this.loader = loader;
    }
    
    static Package getSystemPackage(String name) {
        synchronized (pkgs) {
            Package pkg = (Package)(Package)pkgs.get(name);
            if (pkg == null) {
                name = name.replace('.', '/').concat("/");
                String fn = getSystemPackage0(name);
                if (fn != null) {
                    pkg = defineSystemPackage(name, fn);
                }
            }
            return pkg;
        }
    }
    
    static Package[] getSystemPackages() {
        String[] names = getSystemPackages0();
        synchronized (pkgs) {
            for (int i = 0; i < names.length; i++) {
                defineSystemPackage(names[i], getSystemPackage0(names[i]));
            }
            return (Package[])(Package[])pkgs.values().toArray(new Package[pkgs.size()]);
        }
    }
    
    private static Package defineSystemPackage(final String iname, final String fn) {
        return (Package)(Package)AccessController.doPrivileged(new Package$1(iname, fn));
    }
    
    private static Manifest loadManifest(String fn) {
        try {
            FileInputStream fis = new FileInputStream(fn);
            JarInputStream jis = new JarInputStream(fis, false);
            Manifest man = jis.getManifest();
            jis.close();
            return man;
        } catch (IOException e) {
            return null;
        }
    }
    private static Map pkgs = new HashMap(31);
    private static Map urls = new HashMap(10);
    private static Map mans = new HashMap(10);
    
    private static native String getSystemPackage0(String name);
    
    private static native String[] getSystemPackages0();
    private final String pkgName;
    private final String specTitle;
    private final String specVersion;
    private final String specVendor;
    private final String implTitle;
    private final String implVersion;
    private final String implVendor;
    private final URL sealBase;
    private final transient ClassLoader loader;
    private transient Class packageInfo;
}
