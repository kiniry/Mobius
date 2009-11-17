package java.net;

import java.io.IOException;
import sun.net.util.IPAddressUtil;

public abstract class URLStreamHandler {
    
    public URLStreamHandler() {
        
    }
    
    protected abstract URLConnection openConnection(URL u) throws IOException;
    
    protected URLConnection openConnection(URL u, Proxy p) throws IOException {
        throw new UnsupportedOperationException("Method not implemented.");
    }
    
    protected void parseURL(URL u, String spec, int start, int limit) {
        String protocol = u.getProtocol();
        String authority = u.getAuthority();
        String userInfo = u.getUserInfo();
        String host = u.getHost();
        int port = u.getPort();
        String path = u.getPath();
        String query = u.getQuery();
        String ref = u.getRef();
        boolean isRelPath = false;
        boolean queryOnly = false;
        if (start < limit) {
            int queryStart = spec.indexOf('?');
            queryOnly = queryStart == start;
            if ((queryStart != -1) && (queryStart < limit)) {
                query = spec.substring(queryStart + 1, limit);
                if (limit > queryStart) limit = queryStart;
                spec = spec.substring(0, queryStart);
            }
        }
        int i = 0;
        if ((start <= limit - 2) && (spec.charAt(start) == '/') && (spec.charAt(start + 1) == '/')) {
            start += 2;
            i = spec.indexOf('/', start);
            if (i < 0) {
                i = spec.indexOf('?', start);
                if (i < 0) i = limit;
            }
            host = authority = spec.substring(start, i);
            int ind = authority.indexOf('@');
            if (ind != -1) {
                userInfo = authority.substring(0, ind);
                host = authority.substring(ind + 1);
            } else {
                userInfo = null;
            }
            if (host != null) {
                if (host.length() > 0 && (host.charAt(0) == '[')) {
                    if ((ind = host.indexOf(']')) > 2) {
                        String nhost = host;
                        host = nhost.substring(0, ind + 1);
                        if (!IPAddressUtil.isIPv6LiteralAddress(host.substring(1, ind))) {
                            throw new IllegalArgumentException("Invalid host: " + host);
                        }
                        port = -1;
                        if (nhost.length() > ind + 1) {
                            if (nhost.charAt(ind + 1) == ':') {
                                ++ind;
                                if (nhost.length() > (ind + 1)) {
                                    port = Integer.parseInt(nhost.substring(ind + 1));
                                }
                            } else {
                                throw new IllegalArgumentException("Invalid authority field: " + authority);
                            }
                        }
                    } else {
                        throw new IllegalArgumentException("Invalid authority field: " + authority);
                    }
                } else {
                    ind = host.indexOf(':');
                    port = -1;
                    if (ind >= 0) {
                        if (host.length() > (ind + 1)) {
                            port = Integer.parseInt(host.substring(ind + 1));
                        }
                        host = host.substring(0, ind);
                    }
                }
            } else {
                host = "";
            }
            if (port < -1) throw new IllegalArgumentException("Invalid port number :" + port);
            start = i;
            if (authority != null && authority.length() > 0) path = "";
        }
        if (host == null) {
            host = "";
        }
        if (start < limit) {
            if (spec.charAt(start) == '/') {
                path = spec.substring(start, limit);
            } else if (path != null && path.length() > 0) {
                isRelPath = true;
                int ind = path.lastIndexOf('/');
                String seperator = "";
                if (ind == -1 && authority != null) seperator = "/";
                path = path.substring(0, ind + 1) + seperator + spec.substring(start, limit);
            } else {
                String seperator = (authority != null) ? "/" : "";
                path = seperator + spec.substring(start, limit);
            }
        } else if (queryOnly && path != null) {
            int ind = path.lastIndexOf('/');
            if (ind < 0) ind = 0;
            path = path.substring(0, ind) + "/";
        }
        if (path == null) path = "";
        if (isRelPath) {
            while ((i = path.indexOf("/./")) >= 0) {
                path = path.substring(0, i) + path.substring(i + 2);
            }
            i = 0;
            while ((i = path.indexOf("/../", i)) >= 0) {
                if (i > 0 && (limit = path.lastIndexOf('/', i - 1)) >= 0 && (path.indexOf("/../", limit) != 0)) {
                    path = path.substring(0, limit) + path.substring(i + 3);
                    i = 0;
                } else {
                    i = i + 3;
                }
            }
            while (path.endsWith("/..")) {
                i = path.indexOf("/..");
                if ((limit = path.lastIndexOf('/', i - 1)) >= 0) {
                    path = path.substring(0, limit + 1);
                } else {
                    break;
                }
            }
            if (path.startsWith("./") && path.length() > 2) path = path.substring(2);
            if (path.endsWith("/.")) path = path.substring(0, path.length() - 1);
        }
        setURL(u, protocol, host, port, authority, userInfo, path, query, ref);
    }
    
    protected int getDefaultPort() {
        return -1;
    }
    
    protected boolean equals(URL u1, URL u2) {
        String ref1 = u1.getRef();
        String ref2 = u2.getRef();
        return sameFile(u1, u2) && (ref1 == ref2 || (ref1 != null && ref1.equals(ref2)));
    }
    
    protected int hashCode(URL u) {
        int h = 0;
        String protocol = u.getProtocol();
        if (protocol != null) h += protocol.hashCode();
        InetAddress addr = getHostAddress(u);
        if (addr != null) {
            h += addr.hashCode();
        } else {
            String host = u.getHost();
            if (host != null) h += host.toLowerCase().hashCode();
        }
        String file = u.getFile();
        if (file != null) h += file.hashCode();
        if (u.getPort() == -1) h += getDefaultPort(); else h += u.getPort();
        String ref = u.getRef();
        if (ref != null) h += ref.hashCode();
        return h;
    }
    
    protected boolean sameFile(URL u1, URL u2) {
        if (!((u1.getProtocol() == u2.getProtocol()) || (u1.getProtocol() != null && u1.getProtocol().equalsIgnoreCase(u2.getProtocol())))) return false;
        if (!hostsEqual(u1, u2)) return false;
        if (!(u1.getFile() == u2.getFile() || (u1.getFile() != null && u1.getFile().equals(u2.getFile())))) return false;
        int port1;
        int port2;
        port1 = (u1.getPort() != -1) ? u1.getPort() : u1.handler.getDefaultPort();
        port2 = (u2.getPort() != -1) ? u2.getPort() : u2.handler.getDefaultPort();
        if (port1 != port2) return false;
        return true;
    }
    
    protected synchronized InetAddress getHostAddress(URL u) {
        if (u.hostAddress != null) return u.hostAddress;
        String host = u.getHost();
        if (host == null || host.equals("")) {
            return null;
        } else {
            try {
                u.hostAddress = InetAddress.getByName(host);
            } catch (UnknownHostException ex) {
                return null;
            } catch (SecurityException se) {
                return null;
            }
        }
        return u.hostAddress;
    }
    
    protected boolean hostsEqual(URL u1, URL u2) {
        InetAddress a1 = getHostAddress(u1);
        InetAddress a2 = getHostAddress(u2);
        if (a1 != null && a2 != null) {
            return a1.equals(a2);
        } else if (u1.getHost() != null && u2.getHost() != null) return u1.getHost().equalsIgnoreCase(u2.getHost()); else return u1.getHost() == null && u2.getHost() == null;
    }
    
    protected String toExternalForm(URL u) {
        int len = u.getProtocol().length() + 1;
        if (u.getAuthority() != null && u.getAuthority().length() > 0) len += 2 + u.getAuthority().length();
        if (u.getPath() != null) {
            len += u.getPath().length();
        }
        if (u.getQuery() != null) {
            len += 1 + u.getQuery().length();
        }
        if (u.getRef() != null) len += 1 + u.getRef().length();
        StringBuffer result = new StringBuffer(len);
        result.append(u.getProtocol());
        result.append(":");
        if (u.getAuthority() != null && u.getAuthority().length() > 0) {
            result.append("//");
            result.append(u.getAuthority());
        }
        if (u.getPath() != null) {
            result.append(u.getPath());
        }
        if (u.getQuery() != null) {
            result.append('?');
            result.append(u.getQuery());
        }
        if (u.getRef() != null) {
            result.append("#");
            result.append(u.getRef());
        }
        return result.toString();
    }
    
    protected void setURL(URL u, String protocol, String host, int port, String authority, String userInfo, String path, String query, String ref) {
        if (this != u.handler) {
            throw new SecurityException("handler for url different from this handler");
        }
        u.set(u.getProtocol(), host, port, authority, userInfo, path, query, ref);
    }
    
    
    protected void setURL(URL u, String protocol, String host, int port, String file, String ref) {
        String authority = null;
        String userInfo = null;
        if (host != null && host.length() != 0) {
            authority = (port == -1) ? host : host + ":" + port;
            int at = host.lastIndexOf('@');
            if (at != -1) {
                userInfo = host.substring(0, at);
                host = host.substring(at + 1);
            }
        }
        String path = null;
        String query = null;
        if (file != null) {
            int q = file.lastIndexOf('?');
            if (q != -1) {
                query = file.substring(q + 1);
                path = file.substring(0, q);
            } else path = file;
        }
        setURL(u, protocol, host, port, authority, userInfo, path, query, ref);
    }
}
