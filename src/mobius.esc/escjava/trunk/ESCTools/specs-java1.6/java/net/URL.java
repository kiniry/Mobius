package java.net;

import java.io.IOException;
import java.io.InputStream;
import java.util.Hashtable;
import java.util.StringTokenizer;
import sun.security.util.SecurityConstants;

public final class URL implements java.io.Serializable {
    static final long serialVersionUID = -7627629688361524110L;
    private static final String protocolPathProp = "java.protocol.handler.pkgs";
    private String protocol;
    private String host;
    private int port = -1;
    private String file;
    private transient String query;
    private String authority;
    private transient String path;
    private transient String userInfo;
    private String ref;
    transient InetAddress hostAddress;
    transient URLStreamHandler handler;
    private int hashCode = -1;
    
    public URL(String protocol, String host, int port, String file) throws MalformedURLException {
        this(protocol, host, port, file, null);
    }
    
    public URL(String protocol, String host, String file) throws MalformedURLException {
        this(protocol, host, -1, file);
    }
    
    public URL(String protocol, String host, int port, String file, URLStreamHandler handler) throws MalformedURLException {
        
        if (handler != null) {
            SecurityManager sm = System.getSecurityManager();
            if (sm != null) {
                checkSpecifyHandler(sm);
            }
        }
        protocol = protocol.toLowerCase();
        this.protocol = protocol;
        if (host != null) {
            if (host != null && host.indexOf(':') >= 0 && !host.startsWith("[")) {
                host = "[" + host + "]";
            }
            this.host = host;
            if (port < -1) {
                throw new MalformedURLException("Invalid port number :" + port);
            }
            this.port = port;
            authority = (port == -1) ? host : host + ":" + port;
        }
        Parts parts = new Parts(file);
        path = parts.getPath();
        query = parts.getQuery();
        if (query != null) {
            this.file = path + "?" + query;
        } else {
            this.file = path;
        }
        ref = parts.getRef();
        if (handler == null && (handler = getURLStreamHandler(protocol)) == null) {
            throw new MalformedURLException("unknown protocol: " + protocol);
        }
        this.handler = handler;
    }
    
    public URL(String spec) throws MalformedURLException {
        this(null, spec);
    }
    
    public URL(URL context, String spec) throws MalformedURLException {
        this(context, spec, null);
    }
    
    public URL(URL context, String spec, URLStreamHandler handler) throws MalformedURLException {
        
        String original = spec;
        int i;
        int limit;
        int c;
        int start = 0;
        String newProtocol = null;
        boolean aRef = false;
        boolean isRelative = false;
        if (handler != null) {
            SecurityManager sm = System.getSecurityManager();
            if (sm != null) {
                checkSpecifyHandler(sm);
            }
        }
        try {
            limit = spec.length();
            while ((limit > 0) && (spec.charAt(limit - 1) <= ' ')) {
                limit--;
            }
            while ((start < limit) && (spec.charAt(start) <= ' ')) {
                start++;
            }
            if (spec.regionMatches(true, start, "url:", 0, 4)) {
                start += 4;
            }
            if (start < spec.length() && spec.charAt(start) == '#') {
                aRef = true;
            }
            for (i = start; !aRef && (i < limit) && ((c = spec.charAt(i)) != '/'); i++) {
                if (c == ':') {
                    String s = spec.substring(start, i).toLowerCase();
                    if (isValidProtocol(s)) {
                        newProtocol = s;
                        start = i + 1;
                    }
                    break;
                }
            }
            protocol = newProtocol;
            if ((context != null) && ((newProtocol == null) || newProtocol.equalsIgnoreCase(context.protocol))) {
                if (handler == null) {
                    handler = context.handler;
                }
                if (context.path != null && context.path.startsWith("/")) newProtocol = null;
                if (newProtocol == null) {
                    protocol = context.protocol;
                    authority = context.authority;
                    userInfo = context.userInfo;
                    host = context.host;
                    port = context.port;
                    file = context.file;
                    path = context.path;
                    isRelative = true;
                }
            }
            if (protocol == null) {
                throw new MalformedURLException("no protocol: " + original);
            }
            if (handler == null && (handler = getURLStreamHandler(protocol)) == null) {
                throw new MalformedURLException("unknown protocol: " + protocol);
            }
            this.handler = handler;
            i = spec.indexOf('#', start);
            if (i >= 0) {
                ref = spec.substring(i + 1, limit);
                limit = i;
            }
            if (isRelative && start == limit) {
                query = context.query;
                if (ref == null) {
                    ref = context.ref;
                }
            }
            handler.parseURL(this, spec, start, limit);
        } catch (MalformedURLException e) {
            throw e;
        } catch (Exception e) {
            throw new MalformedURLException(e.getMessage());
        }
    }
    
    private boolean isValidProtocol(String protocol) {
        int len = protocol.length();
        if (len < 1) return false;
        char c = protocol.charAt(0);
        if (!Character.isLetter(c)) return false;
        for (int i = 1; i < len; i++) {
            c = protocol.charAt(i);
            if (!Character.isLetterOrDigit(c) && c != '.' && c != '+' && c != '-') {
                return false;
            }
        }
        return true;
    }
    
    private void checkSpecifyHandler(SecurityManager sm) {
        sm.checkPermission(SecurityConstants.SPECIFY_HANDLER_PERMISSION);
    }
    
    protected void set(String protocol, String host, int port, String file, String ref) {
        synchronized (this) {
            this.protocol = protocol;
            this.host = host;
            authority = port == -1 ? host : host + ":" + port;
            this.port = port;
            this.file = file;
            this.ref = ref;
            hashCode = -1;
            hostAddress = null;
            int q = file.lastIndexOf('?');
            if (q != -1) {
                query = file.substring(q + 1);
                path = file.substring(0, q);
            } else path = file;
        }
    }
    
    protected void set(String protocol, String host, int port, String authority, String userInfo, String path, String query, String ref) {
        synchronized (this) {
            this.protocol = protocol;
            this.host = host;
            this.port = port;
            this.file = query == null ? path : path + "?" + query;
            this.userInfo = userInfo;
            this.path = path;
            this.ref = ref;
            hashCode = -1;
            hostAddress = null;
            this.query = query;
            this.authority = authority;
        }
    }
    
    public String getQuery() {
        return query;
    }
    
    public String getPath() {
        return path;
    }
    
    public String getUserInfo() {
        return userInfo;
    }
    
    public String getAuthority() {
        return authority;
    }
    
    public int getPort() {
        return port;
    }
    
    public int getDefaultPort() {
        return handler.getDefaultPort();
    }
    
    public String getProtocol() {
        return protocol;
    }
    
    public String getHost() {
        return host;
    }
    
    public String getFile() {
        return file;
    }
    
    public String getRef() {
        return ref;
    }
    
    public boolean equals(Object obj) {
        if (!(obj instanceof URL)) return false;
        URL u2 = (URL)(URL)obj;
        return handler.equals(this, u2);
    }
    
    public synchronized int hashCode() {
        if (hashCode != -1) return hashCode;
        hashCode = handler.hashCode(this);
        return hashCode;
    }
    
    public boolean sameFile(URL other) {
        return handler.sameFile(this, other);
    }
    
    public String toString() {
        return toExternalForm();
    }
    
    public String toExternalForm() {
        return handler.toExternalForm(this);
    }
    
    public URI toURI() throws URISyntaxException {
        return new URI(toString());
    }
    
    public URLConnection openConnection() throws java.io.IOException {
        return handler.openConnection(this);
    }
    
    public URLConnection openConnection(Proxy proxy) throws java.io.IOException {
        if (proxy == null) {
            throw new IllegalArgumentException("proxy can not be null");
        }
        SecurityManager sm = System.getSecurityManager();
        if (proxy.type() != Proxy$Type.DIRECT && sm != null) {
            InetSocketAddress epoint = (InetSocketAddress)(InetSocketAddress)proxy.address();
            if (epoint.isUnresolved()) sm.checkConnect(epoint.getHostName(), epoint.getPort()); else sm.checkConnect(epoint.getAddress().getHostAddress(), epoint.getPort());
        }
        return handler.openConnection(this, proxy);
    }
    
    public final InputStream openStream() throws java.io.IOException {
        return openConnection().getInputStream();
    }
    
    public final Object getContent() throws java.io.IOException {
        return openConnection().getContent();
    }
    
    public final Object getContent(Class[] classes) throws java.io.IOException {
        return openConnection().getContent(classes);
    }
    static URLStreamHandlerFactory factory;
    
    public static void setURLStreamHandlerFactory(URLStreamHandlerFactory fac) {
        synchronized (streamHandlerLock) {
            if (factory != null) {
                throw new Error("factory already defined");
            }
            SecurityManager security = System.getSecurityManager();
            if (security != null) {
                security.checkSetFactory();
            }
            handlers.clear();
            factory = fac;
        }
    }
    static Hashtable handlers = new Hashtable();
    private static Object streamHandlerLock = new Object();
    
    static URLStreamHandler getURLStreamHandler(String protocol) {
        URLStreamHandler handler = (URLStreamHandler)(URLStreamHandler)handlers.get(protocol);
        if (handler == null) {
            boolean checkedWithFactory = false;
            if (factory != null) {
                handler = factory.createURLStreamHandler(protocol);
                checkedWithFactory = true;
            }
            if (handler == null) {
                String packagePrefixList = null;
                packagePrefixList = (String)(String)java.security.AccessController.doPrivileged(new sun.security.action.GetPropertyAction(protocolPathProp, ""));
                if (packagePrefixList != "") {
                    packagePrefixList += "|";
                }
                packagePrefixList += "sun.net.www.protocol";
                StringTokenizer packagePrefixIter = new StringTokenizer(packagePrefixList, "|");
                while (handler == null && packagePrefixIter.hasMoreTokens()) {
                    String packagePrefix = packagePrefixIter.nextToken().trim();
                    try {
                        String clsName = packagePrefix + "." + protocol + ".Handler";
                        Class cls = null;
                        try {
                            cls = Class.forName(clsName);
                        } catch (ClassNotFoundException e) {
                            ClassLoader cl = ClassLoader.getSystemClassLoader();
                            if (cl != null) {
                                cls = cl.loadClass(clsName);
                            }
                        }
                        if (cls != null) {
                            handler = (URLStreamHandler)(URLStreamHandler)cls.newInstance();
                        }
                    } catch (Exception e) {
                    }
                }
            }
            synchronized (streamHandlerLock) {
                URLStreamHandler handler2 = null;
                handler2 = (URLStreamHandler)(URLStreamHandler)handlers.get(protocol);
                if (handler2 != null) {
                    return handler2;
                }
                if (!checkedWithFactory && factory != null) {
                    handler2 = factory.createURLStreamHandler(protocol);
                }
                if (handler2 != null) {
                    handler = handler2;
                }
                if (handler != null) {
                    handlers.put(protocol, handler);
                }
            }
        }
        return handler;
    }
    
    private synchronized void writeObject(java.io.ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
    }
    
    private synchronized void readObject(java.io.ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        if ((handler = getURLStreamHandler(protocol)) == null) {
            throw new IOException("unknown protocol: " + protocol);
        }
        if (authority == null && ((host != null && host.length() > 0) || port != -1)) {
            if (host == null) host = "";
            authority = (port == -1) ? host : host + ":" + port;
            int at = host.lastIndexOf('@');
            if (at != -1) {
                userInfo = host.substring(0, at);
                host = host.substring(at + 1);
            }
        } else if (authority != null) {
            int ind = authority.indexOf('@');
            if (ind != -1) userInfo = authority.substring(0, ind);
        }
        path = null;
        query = null;
        if (file != null) {
            int q = file.lastIndexOf('?');
            if (q != -1) {
                query = file.substring(q + 1);
                path = file.substring(0, q);
            } else path = file;
        }
    }
}
