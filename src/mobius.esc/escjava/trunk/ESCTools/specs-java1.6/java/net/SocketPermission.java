package java.net;

import java.util.StringTokenizer;
import java.net.InetAddress;
import java.security.Permission;
import java.security.PermissionCollection;
import java.io.IOException;
import sun.net.util.IPAddressUtil;
import sun.security.util.SecurityConstants;
import sun.security.util.Debug;

public final class SocketPermission extends Permission implements java.io.Serializable {
    private static final long serialVersionUID = -7204263841984476862L;
    private static final int CONNECT = 1;
    private static final int LISTEN = 2;
    private static final int ACCEPT = 4;
    private static final int RESOLVE = 8;
    private static final int NONE = 0;
    private static final int ALL = CONNECT | LISTEN | ACCEPT | RESOLVE;
    private static final int PORT_MIN = 0;
    private static final int PORT_MAX = 65535;
    private static final int PRIV_PORT_MAX = 1023;
    private transient int mask;
    private String actions;
    private transient String hostname;
    private transient String cname;
    private transient InetAddress[] addresses;
    private transient boolean wildcard;
    private transient boolean init_with_ip;
    private transient boolean invalid;
    private transient int[] portrange;
    private transient boolean defaultDeny = false;
    private transient boolean untrusted;
    private static boolean trustProxy;
    private static boolean trustNameService;
    private static Debug debug = null;
    private static boolean debugInit = false;
    static {
        Boolean tmp = (Boolean)(Boolean)java.security.AccessController.doPrivileged(new sun.security.action.GetBooleanAction("trustProxy"));
        trustProxy = tmp.booleanValue();
        tmp = (Boolean)(Boolean)java.security.AccessController.doPrivileged(new sun.security.action.GetBooleanAction("sun.net.trustNameService"));
        trustNameService = tmp.booleanValue();
    }
    
    private static synchronized Debug getDebug() {
        if (!debugInit) {
            debug = Debug.getInstance("access");
            debugInit = true;
        }
        return debug;
    }
    
    public SocketPermission(String host, String action) {
        super(getHost(host));
        init(getName(), getMask(action));
    }
    
    SocketPermission(String host, int mask) {
        super(getHost(host));
        init(getName(), mask);
    }
    
    private void setDeny() {
        defaultDeny = true;
    }
    
    private static String getHost(String host) {
        if (host.equals("")) {
            return "localhost";
        } else {
            int ind;
            if (host.charAt(0) != '[') {
                if ((ind = host.indexOf(':')) != host.lastIndexOf(':')) {
                    StringTokenizer st = new StringTokenizer(host, ":");
                    int tokens = st.countTokens();
                    if (tokens == 9) {
                        ind = host.lastIndexOf(':');
                        host = "[" + host.substring(0, ind) + "]" + host.substring(ind);
                    } else if (tokens == 8 && host.indexOf("::") == -1) {
                        host = "[" + host + "]";
                    } else {
                        throw new IllegalArgumentException("Ambiguous hostport part");
                    }
                }
            }
            return host;
        }
    }
    
    private int[] parsePort(String port) throws Exception {
        if (port == null || port.equals("") || port.equals("*")) {
            return new int[]{PORT_MIN, PORT_MAX};
        }
        int dash = port.indexOf('-');
        if (dash == -1) {
            int p = Integer.parseInt(port);
            return new int[]{p, p};
        } else {
            String low = port.substring(0, dash);
            String high = port.substring(dash + 1);
            int l;
            int h;
            if (low.equals("")) {
                l = PORT_MIN;
            } else {
                l = Integer.parseInt(low);
            }
            if (high.equals("")) {
                h = PORT_MAX;
            } else {
                h = Integer.parseInt(high);
            }
            if (l < 0 || h < 0 || h < l) throw new IllegalArgumentException("invalid port range");
            return new int[]{l, h};
        }
    }
    
    private void init(String host, int mask) {
        if ((mask & ALL) != mask) throw new IllegalArgumentException("invalid actions mask");
        this.mask = mask | RESOLVE;
        int rb = 0;
        int start = 0;
        int end = 0;
        int sep = -1;
        String hostport = host;
        if (host.charAt(0) == '[') {
            start = 1;
            rb = host.indexOf(']');
            if (rb != -1) {
                host = host.substring(start, rb);
            } else {
                throw new IllegalArgumentException("invalid host/port: " + host);
            }
            sep = hostport.indexOf(':', rb + 1);
        } else {
            start = 0;
            sep = host.indexOf(':', rb);
            end = sep;
            if (sep != -1) {
                host = host.substring(start, end);
            }
        }
        if (sep != -1) {
            String port = hostport.substring(sep + 1);
            try {
                portrange = parsePort(port);
            } catch (Exception e) {
                throw new IllegalArgumentException("invalid port range: " + port);
            }
        } else {
            portrange = new int[]{PORT_MIN, PORT_MAX};
        }
        hostname = host;
        if (host.lastIndexOf('*') > 0) {
            throw new IllegalArgumentException("invalid host wildcard specification");
        } else if (host.startsWith("*")) {
            wildcard = true;
            if (host.equals("*")) {
                cname = "";
            } else if (host.startsWith("*.")) {
                cname = host.substring(1).toLowerCase();
            } else {
                throw new IllegalArgumentException("invalid host wildcard specification");
            }
            return;
        } else {
            if (host.length() > 0) {
                char ch = host.charAt(0);
                if (ch == ':' || Character.digit(ch, 16) != -1) {
                    byte[] ip = IPAddressUtil.textToNumericFormatV4(host);
                    if (ip == null) {
                        ip = IPAddressUtil.textToNumericFormatV6(host);
                    }
                    if (ip != null) {
                        try {
                            addresses = new InetAddress[]{InetAddress.getByAddress(ip)};
                            init_with_ip = true;
                        } catch (UnknownHostException uhe) {
                            invalid = true;
                        }
                    }
                }
            }
        }
    }
    
    private static int getMask(String action) {
        if (action == null) {
            throw new NullPointerException("action can\'t be null");
        }
        if (action.equals("")) {
            throw new IllegalArgumentException("action can\'t be empty");
        }
        int mask = NONE;
        if (action == SecurityConstants.SOCKET_RESOLVE_ACTION) {
            return RESOLVE;
        } else if (action == SecurityConstants.SOCKET_CONNECT_ACTION) {
            return CONNECT;
        } else if (action == SecurityConstants.SOCKET_LISTEN_ACTION) {
            return LISTEN;
        } else if (action == SecurityConstants.SOCKET_ACCEPT_ACTION) {
            return ACCEPT;
        } else if (action == SecurityConstants.SOCKET_CONNECT_ACCEPT_ACTION) {
            return CONNECT | ACCEPT;
        }
        char[] a = action.toCharArray();
        int i = a.length - 1;
        if (i < 0) return mask;
        while (i != -1) {
            char c;
            while ((i != -1) && ((c = a[i]) == ' ' || c == '\r' || c == '\n' || c == '\f' || c == '\t')) i--;
            int matchlen;
            if (i >= 6 && (a[i - 6] == 'c' || a[i - 6] == 'C') && (a[i - 5] == 'o' || a[i - 5] == 'O') && (a[i - 4] == 'n' || a[i - 4] == 'N') && (a[i - 3] == 'n' || a[i - 3] == 'N') && (a[i - 2] == 'e' || a[i - 2] == 'E') && (a[i - 1] == 'c' || a[i - 1] == 'C') && (a[i] == 't' || a[i] == 'T')) {
                matchlen = 7;
                mask |= CONNECT;
            } else if (i >= 6 && (a[i - 6] == 'r' || a[i - 6] == 'R') && (a[i - 5] == 'e' || a[i - 5] == 'E') && (a[i - 4] == 's' || a[i - 4] == 'S') && (a[i - 3] == 'o' || a[i - 3] == 'O') && (a[i - 2] == 'l' || a[i - 2] == 'L') && (a[i - 1] == 'v' || a[i - 1] == 'V') && (a[i] == 'e' || a[i] == 'E')) {
                matchlen = 7;
                mask |= RESOLVE;
            } else if (i >= 5 && (a[i - 5] == 'l' || a[i - 5] == 'L') && (a[i - 4] == 'i' || a[i - 4] == 'I') && (a[i - 3] == 's' || a[i - 3] == 'S') && (a[i - 2] == 't' || a[i - 2] == 'T') && (a[i - 1] == 'e' || a[i - 1] == 'E') && (a[i] == 'n' || a[i] == 'N')) {
                matchlen = 6;
                mask |= LISTEN;
            } else if (i >= 5 && (a[i - 5] == 'a' || a[i - 5] == 'A') && (a[i - 4] == 'c' || a[i - 4] == 'C') && (a[i - 3] == 'c' || a[i - 3] == 'C') && (a[i - 2] == 'e' || a[i - 2] == 'E') && (a[i - 1] == 'p' || a[i - 1] == 'P') && (a[i] == 't' || a[i] == 'T')) {
                matchlen = 6;
                mask |= ACCEPT;
            } else {
                throw new IllegalArgumentException("invalid permission: " + action);
            }
            boolean seencomma = false;
            while (i >= matchlen && !seencomma) {
                switch (a[i - matchlen]) {
                case ',': 
                    seencomma = true;
                
                case ' ': 
                
                case '\r': 
                
                case '\n': 
                
                case '\f': 
                
                case '\t': 
                    break;
                
                default: 
                    throw new IllegalArgumentException("invalid permission: " + action);
                
                }
                i--;
            }
            i -= matchlen;
        }
        return mask;
    }
    
    void getCanonName() throws UnknownHostException {
        if (cname != null || invalid || untrusted) return;
        try {
            if (addresses == null) {
                getIP();
            }
            if (init_with_ip) {
                cname = addresses[0].getHostName(false).toLowerCase();
            } else {
                cname = InetAddress.getByName(addresses[0].getHostAddress()).getHostName(false).toLowerCase();
                if (!trustNameService && sun.net.www.URLConnection.isProxiedHost(hostname)) {
                    if (!match(cname, hostname) && (defaultDeny || !cname.equals(addresses[0].getHostAddress()))) {
                        if (!authorized(hostname, addresses[0].getAddress())) {
                            untrusted = true;
                            Debug debug = getDebug();
                            if (debug != null && Debug.isOn("failure")) {
                                debug.println("socket access restriction: proxied host " + "(" + addresses[0] + ")" + " does not match " + cname + " from reverse lookup");
                            }
                        }
                    }
                }
            }
        } catch (UnknownHostException uhe) {
            invalid = true;
            throw uhe;
        }
    }
    
    private boolean match(String cname, String hname) {
        String a = cname.toLowerCase();
        String b = hname.toLowerCase();
        if (a.startsWith(b) && ((a.length() == b.length()) || (a.charAt(b.length()) == '.'))) return true;
        if (b.endsWith(".akamai.net") || b.endsWith(".akamai.com")) return true;
        String af = fragment(a);
        String bf = fragment(b);
        return af.length() != 0 && bf.length() != 0 && fragment(a).equals(fragment(b));
    }
    
    private String fragment(String cname) {
        int dot;
        dot = cname.lastIndexOf('.');
        if (dot == -1) return cname;
        if (dot == 0) return "";
        if (dot == cname.length() - 1) {
            cname = cname.substring(0, cname.length() - 1);
            dot = cname.lastIndexOf('.');
        }
        if (dot < 1) return "";
        int second = cname.lastIndexOf('.', dot - 1);
        if (second == -1) return cname;
        if (((cname.length() - dot) <= 3) && ((dot - second) <= 4) && second > 0) {
            if (dot - second == 4) {
                String s = cname.substring(second + 1, dot);
                if (!(s.equals("com") || s.equals("org") || s.equals("edu"))) {
                    return cname.substring(second + 1);
                }
            }
            int third = cname.lastIndexOf('.', second - 1);
            if (third == -1) return cname.substring(second + 1); else return cname.substring(third + 1);
        }
        return cname.substring(second + 1);
    }
    
    private boolean authorized(String cname, byte[] addr) {
        if (addr.length == 4) return authorizedIPv4(cname, addr); else if (addr.length == 16) return authorizedIPv6(cname, addr); else return false;
    }
    
    private boolean authorizedIPv4(String cname, byte[] addr) {
        String authHost = "";
        InetAddress auth;
        try {
            authHost = "auth." + (addr[3] & 255) + "." + (addr[2] & 255) + "." + (addr[1] & 255) + "." + (addr[0] & 255) + ".in-addr.arpa";
            authHost = hostname + '.' + authHost;
            auth = InetAddress.getAllByName0(authHost, false)[0];
            if (auth.equals(InetAddress.getByAddress(addr))) return true;
            Debug debug = getDebug();
            if (debug != null && Debug.isOn("failure")) {
                debug.println("socket access restriction: IP address of " + auth + " != " + InetAddress.getByAddress(addr));
            }
        } catch (UnknownHostException uhe) {
            Debug debug = getDebug();
            if (debug != null && Debug.isOn("failure")) {
                debug.println("socket access restriction: forward lookup failed for " + authHost);
            }
        } catch (IOException x) {
        }
        return false;
    }
    
    private boolean authorizedIPv6(String cname, byte[] addr) {
        String authHost = "";
        InetAddress auth;
        try {
            StringBuffer sb = new StringBuffer(39);
            for (int i = 15; i >= 0; i--) {
                sb.append(Integer.toHexString(((addr[i]) & 15)));
                sb.append('.');
                sb.append(Integer.toHexString(((addr[i] >> 4) & 15)));
                sb.append('.');
            }
            authHost = "auth." + sb.toString() + "IP6.ARPA";
            authHost = hostname + '.' + authHost;
            auth = InetAddress.getAllByName0(authHost, false)[0];
            if (auth.equals(InetAddress.getByAddress(addr))) return true;
            Debug debug = getDebug();
            if (debug != null && Debug.isOn("failure")) {
                debug.println("socket access restriction: IP address of " + auth + " != " + InetAddress.getByAddress(addr));
            }
        } catch (UnknownHostException uhe) {
            Debug debug = getDebug();
            if (debug != null && Debug.isOn("failure")) {
                debug.println("socket access restriction: forward lookup failed for " + authHost);
            }
        } catch (IOException x) {
        }
        return false;
    }
    
    void getIP() throws UnknownHostException {
        if (addresses != null || wildcard || invalid) return;
        try {
            String host;
            if (getName().charAt(0) == '[') {
                host = getName().substring(1, getName().indexOf(']'));
            } else {
                int i = getName().indexOf(":");
                if (i == -1) host = getName(); else {
                    host = getName().substring(0, i);
                }
            }
            addresses = new InetAddress[]{InetAddress.getAllByName0(host, false)[0]};
        } catch (UnknownHostException uhe) {
            invalid = true;
            throw uhe;
        } catch (IndexOutOfBoundsException iobe) {
            invalid = true;
            throw new UnknownHostException(getName());
        }
    }
    
    public boolean implies(Permission p) {
        int i;
        int j;
        if (!(p instanceof SocketPermission)) return false;
        SocketPermission that = (SocketPermission)(SocketPermission)p;
        return ((this.mask & that.mask) == that.mask) && impliesIgnoreMask(that);
    }
    
    boolean impliesIgnoreMask(SocketPermission that) {
        int i;
        int j;
        if ((that.mask & RESOLVE) != that.mask) {
            if ((that.portrange[0] < this.portrange[0]) || (that.portrange[1] > this.portrange[1])) {
                return false;
            }
        }
        if (this.wildcard && "".equals(this.cname)) return true;
        if (this.invalid || that.invalid) {
            return (trustProxy ? inProxyWeTrust(that) : false);
        }
        try {
            if (this.init_with_ip) {
                if (that.wildcard) return false;
                if (that.init_with_ip) {
                    return (this.addresses[0].equals(that.addresses[0]));
                } else {
                    if (that.addresses == null) {
                        that.getIP();
                    }
                    for (i = 0; i < that.addresses.length; i++) {
                        if (this.addresses[0].equals(that.addresses[i])) return true;
                    }
                }
                return false;
            }
            if (this.wildcard || that.wildcard) {
                if (this.wildcard && that.wildcard) return (that.cname.endsWith(this.cname));
                if (that.wildcard) return false;
                if (that.cname == null) {
                    that.getCanonName();
                }
                return (that.cname.endsWith(this.cname));
            }
            if (this.cname == null) {
                this.getCanonName();
            }
            if (this.addresses == null) {
                this.getIP();
            }
            if (that.addresses == null) {
                that.getIP();
            }
            if (!(that.init_with_ip && this.untrusted)) {
                for (j = 0; j < this.addresses.length; j++) {
                    for (i = 0; i < that.addresses.length; i++) {
                        if (this.addresses[j].equals(that.addresses[i])) return true;
                    }
                }
                if (that.cname == null) {
                    that.getCanonName();
                }
                return (this.cname.equalsIgnoreCase(that.cname));
            }
        } catch (UnknownHostException uhe) {
            if (trustProxy) return inProxyWeTrust(that);
        }
        return false;
    }
    
    private boolean inProxyWeTrust(SocketPermission that) {
        String thisHost = hostname;
        String thatHost = that.hostname;
        if (thisHost == null) return false; else return thisHost.equalsIgnoreCase(thatHost);
    }
    
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (!(obj instanceof SocketPermission)) return false;
        SocketPermission that = (SocketPermission)(SocketPermission)obj;
        if (this.mask != that.mask) return false;
        if ((that.mask & RESOLVE) != that.mask) {
            if ((this.portrange[0] != that.portrange[0]) || (this.portrange[1] != that.portrange[1])) {
                return false;
            }
        }
        if (this.getName().equalsIgnoreCase(that.getName())) {
            return true;
        }
        try {
            this.getCanonName();
            that.getCanonName();
        } catch (UnknownHostException uhe) {
            return false;
        }
        if (this.invalid || that.invalid) return false;
        if (this.cname != null) {
            return this.cname.equalsIgnoreCase(that.cname);
        }
        return false;
    }
    
    public int hashCode() {
        if (init_with_ip || wildcard) {
            return this.getName().hashCode();
        }
        try {
            getCanonName();
        } catch (UnknownHostException uhe) {
        }
        if (invalid || cname == null) return this.getName().hashCode(); else return this.cname.hashCode();
    }
    
    int getMask() {
        return mask;
    }
    
    private static String getActions(int mask) {
        StringBuilder sb = new StringBuilder();
        boolean comma = false;
        if ((mask & CONNECT) == CONNECT) {
            comma = true;
            sb.append("connect");
        }
        if ((mask & LISTEN) == LISTEN) {
            if (comma) sb.append(','); else comma = true;
            sb.append("listen");
        }
        if ((mask & ACCEPT) == ACCEPT) {
            if (comma) sb.append(','); else comma = true;
            sb.append("accept");
        }
        if ((mask & RESOLVE) == RESOLVE) {
            if (comma) sb.append(','); else comma = true;
            sb.append("resolve");
        }
        return sb.toString();
    }
    
    public String getActions() {
        if (actions == null) actions = getActions(this.mask);
        return actions;
    }
    
    public PermissionCollection newPermissionCollection() {
        return new SocketPermissionCollection();
    }
    
    private synchronized void writeObject(java.io.ObjectOutputStream s) throws IOException {
        if (actions == null) getActions();
        s.defaultWriteObject();
    }
    
    private synchronized void readObject(java.io.ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        init(getName(), getMask(actions));
    }
}
