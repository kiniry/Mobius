package java.net;

import java.io.File;
import java.io.FilePermission;
import java.io.IOException;
import java.net.URL;
import java.net.URLConnection;
import java.net.URLStreamHandlerFactory;
import java.util.Enumeration;
import java.util.jar.Manifest;
import java.util.jar.Attributes;
import java.util.jar.Attributes.Name;
import java.security.CodeSigner;
import java.security.AccessController;
import java.security.AccessControlContext;
import java.security.SecureClassLoader;
import java.security.CodeSource;
import java.security.Permission;
import java.security.PermissionCollection;
import sun.misc.Resource;
import sun.misc.URLClassPath;
import sun.net.www.ParseUtil;
import sun.security.util.SecurityConstants;

public class URLClassLoader extends SecureClassLoader {
    
    /*synthetic*/ static AccessControlContext access$200(URLClassLoader x0) {
        return x0.acc;
    }
    
    /*synthetic*/ static Class access$100(URLClassLoader x0, String x1, Resource x2) throws IOException {
        return x0.defineClass(x1, x2);
    }
    
    /*synthetic*/ static URLClassPath access$000(URLClassLoader x0) {
        return x0.ucp;
    }
    private URLClassPath ucp;
    private AccessControlContext acc;
    
    public URLClassLoader(URL[] urls, ClassLoader parent) {
        super(parent);
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkCreateClassLoader();
        }
        ucp = new URLClassPath(urls);
        acc = AccessController.getContext();
    }
    
    public URLClassLoader(URL[] urls) {
        
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkCreateClassLoader();
        }
        ucp = new URLClassPath(urls);
        acc = AccessController.getContext();
    }
    
    public URLClassLoader(URL[] urls, ClassLoader parent, URLStreamHandlerFactory factory) {
        super(parent);
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkCreateClassLoader();
        }
        ucp = new URLClassPath(urls, factory);
        acc = AccessController.getContext();
    }
    
    protected void addURL(URL url) {
        ucp.addURL(url);
    }
    
    public URL[] getURLs() {
        return ucp.getURLs();
    }
    
    protected Class findClass(final String name) throws ClassNotFoundException {
        try {
            return (Class)(Class)AccessController.doPrivileged(new URLClassLoader$1(this, name), acc);
        } catch (java.security.PrivilegedActionException pae) {
            throw (ClassNotFoundException)(ClassNotFoundException)pae.getException();
        }
    }
    
    private Class defineClass(String name, Resource res) throws IOException {
        int i = name.lastIndexOf('.');
        URL url = res.getCodeSourceURL();
        if (i != -1) {
            String pkgname = name.substring(0, i);
            Package pkg = getPackage(pkgname);
            Manifest man = res.getManifest();
            if (pkg != null) {
                if (pkg.isSealed()) {
                    if (!pkg.isSealed(url)) {
                        throw new SecurityException("sealing violation: package " + pkgname + " is sealed");
                    }
                } else {
                    if ((man != null) && isSealed(pkgname, man)) {
                        throw new SecurityException("sealing violation: can\'t seal package " + pkgname + ": already loaded");
                    }
                }
            } else {
                if (man != null) {
                    definePackage(pkgname, man, url);
                } else {
                    definePackage(pkgname, null, null, null, null, null, null, null);
                }
            }
        }
        java.nio.ByteBuffer bb = res.getByteBuffer();
        if (bb != null) {
            CodeSigner[] signers = res.getCodeSigners();
            CodeSource cs = new CodeSource(url, signers);
            return defineClass(name, bb, cs);
        } else {
            byte[] b = res.getBytes();
            CodeSigner[] signers = res.getCodeSigners();
            CodeSource cs = new CodeSource(url, signers);
            return defineClass(name, b, 0, b.length, cs);
        }
    }
    
    protected Package definePackage(String name, Manifest man, URL url) throws IllegalArgumentException {
        String path = name.replace('.', '/').concat("/");
        String specTitle = null;
        String specVersion = null;
        String specVendor = null;
        String implTitle = null;
        String implVersion = null;
        String implVendor = null;
        String sealed = null;
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
        return definePackage(name, specTitle, specVersion, specVendor, implTitle, implVersion, implVendor, sealBase);
    }
    
    private boolean isSealed(String name, Manifest man) {
        String path = name.replace('.', '/').concat("/");
        Attributes attr = man.getAttributes(path);
        String sealed = null;
        if (attr != null) {
            sealed = attr.getValue(Attributes$Name.SEALED);
        }
        if (sealed == null) {
            if ((attr = man.getMainAttributes()) != null) {
                sealed = attr.getValue(Attributes$Name.SEALED);
            }
        }
        return "true".equalsIgnoreCase(sealed);
    }
    
    public URL findResource(final String name) {
        URL url = (URL)(URL)AccessController.doPrivileged(new URLClassLoader$2(this, name), acc);
        return url != null ? ucp.checkURL(url) : null;
    }
    
    public Enumeration findResources(final String name) throws IOException {
        final Enumeration e = ucp.findResources(name, true);
        return new URLClassLoader$3(this, e);
    }
    
    protected PermissionCollection getPermissions(CodeSource codesource) {
        PermissionCollection perms = super.getPermissions(codesource);
        URL url = codesource.getLocation();
        Permission p;
        URLConnection urlConnection;
        try {
            urlConnection = url.openConnection();
            p = urlConnection.getPermission();
        } catch (java.io.IOException ioe) {
            p = null;
            urlConnection = null;
        }
        if (p instanceof FilePermission) {
            String path = p.getName();
            if (path.endsWith(File.separator)) {
                path += "-";
                p = new FilePermission(path, SecurityConstants.FILE_READ_ACTION);
            }
        } else if ((p == null) && (url.getProtocol().equals("file"))) {
            String path = url.getFile().replace('/', File.separatorChar);
            path = ParseUtil.decode(path);
            if (path.endsWith(File.separator)) path += "-";
            p = new FilePermission(path, SecurityConstants.FILE_READ_ACTION);
        } else {
            URL locUrl = url;
            if (urlConnection instanceof JarURLConnection) {
                locUrl = ((JarURLConnection)(JarURLConnection)urlConnection).getJarFileURL();
            }
            String host = locUrl.getHost();
            if (host != null && (host.length() > 0)) p = new SocketPermission(host, SecurityConstants.SOCKET_CONNECT_ACCEPT_ACTION);
        }
        if (p != null) {
            final SecurityManager sm = System.getSecurityManager();
            if (sm != null) {
                final Permission fp = p;
                AccessController.doPrivileged(new URLClassLoader$4(this, sm, fp), acc);
            }
            perms.add(p);
        }
        return perms;
    }
    
    public static URLClassLoader newInstance(final URL[] urls, final ClassLoader parent) {
        AccessControlContext acc = AccessController.getContext();
        URLClassLoader ucl = (URLClassLoader)(URLClassLoader)AccessController.doPrivileged(new URLClassLoader$5(urls, parent));
        ucl.acc = acc;
        return ucl;
    }
    
    public static URLClassLoader newInstance(final URL[] urls) {
        AccessControlContext acc = AccessController.getContext();
        URLClassLoader ucl = (URLClassLoader)(URLClassLoader)AccessController.doPrivileged(new URLClassLoader$6(urls));
        ucl.acc = acc;
        return ucl;
    }
}
