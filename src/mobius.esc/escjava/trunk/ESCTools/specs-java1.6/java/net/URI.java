package java.net;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.CharsetDecoder;
import java.nio.charset.CoderResult;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.CharacterCodingException;
import sun.nio.cs.ThreadLocalCoders;
import sun.text.Normalizer;
import java.lang.Character;

public final class URI implements Comparable, Serializable {
    
    /*synthetic*/ static long access$3400() {
        return H_DASH;
    }
    
    /*synthetic*/ static long access$3300() {
        return L_DASH;
    }
    
    /*synthetic*/ static long access$3200() {
        return H_DOT;
    }
    
    /*synthetic*/ static long access$3100() {
        return L_DOT;
    }
    
    /*synthetic*/ static long access$3000() {
        return L_DIGIT;
    }
    
    /*synthetic*/ static long access$2900() {
        return H_ALPHANUM;
    }
    
    /*synthetic*/ static long access$2800() {
        return L_ALPHANUM;
    }
    
    /*synthetic*/ static long access$2700() {
        return H_USERINFO;
    }
    
    /*synthetic*/ static long access$2600() {
        return L_USERINFO;
    }
    
    /*synthetic*/ static int access$2502(URI x0, int x1) {
        return x0.port = x1;
    }
    
    /*synthetic*/ static String access$2402(URI x0, String x1) {
        return x0.host = x1;
    }
    
    /*synthetic*/ static String access$2302(URI x0, String x1) {
        return x0.userInfo = x1;
    }
    
    /*synthetic*/ static String access$2202(URI x0, String x1) {
        return x0.authority = x1;
    }
    
    /*synthetic*/ static long access$2100() {
        return H_REG_NAME;
    }
    
    /*synthetic*/ static long access$2000() {
        return L_REG_NAME;
    }
    
    /*synthetic*/ static long access$1900() {
        return H_SERVER;
    }
    
    /*synthetic*/ static long access$1800() {
        return L_SERVER;
    }
    
    /*synthetic*/ static long access$1700() {
        return H_SERVER_PERCENT;
    }
    
    /*synthetic*/ static long access$1600() {
        return L_SERVER_PERCENT;
    }
    
    /*synthetic*/ static String access$1502(URI x0, String x1) {
        return x0.query = x1;
    }
    
    /*synthetic*/ static String access$1402(URI x0, String x1) {
        return x0.path = x1;
    }
    
    /*synthetic*/ static long access$1300() {
        return H_PATH;
    }
    
    /*synthetic*/ static long access$1200() {
        return L_PATH;
    }
    
    /*synthetic*/ static String access$1102(URI x0, String x1) {
        return x0.fragment = x1;
    }
    
    /*synthetic*/ static String access$1002(URI x0, String x1) {
        return x0.schemeSpecificPart = x1;
    }
    
    /*synthetic*/ static long access$900() {
        return H_URIC;
    }
    
    /*synthetic*/ static long access$800() {
        return L_URIC;
    }
    
    /*synthetic*/ static String access$702(URI x0, String x1) {
        return x0.scheme = x1;
    }
    
    /*synthetic*/ static long access$600() {
        return H_SCHEME;
    }
    
    /*synthetic*/ static long access$500() {
        return L_SCHEME;
    }
    
    /*synthetic*/ static long access$400() {
        return H_ALPHA;
    }
    
    /*synthetic*/ static boolean access$300(char x0, long x1, long x2) {
        return match(x0, x1, x2);
    }
    
    /*synthetic*/ static long access$200() {
        return H_HEX;
    }
    
    /*synthetic*/ static long access$100() {
        return L_HEX;
    }
    
    /*synthetic*/ static String access$002(URI x0, String x1) {
        return x0.string = x1;
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !URI.class.desiredAssertionStatus();
    static final long serialVersionUID = -6052424284110960213L;
    private transient String scheme;
    private transient String fragment;
    private transient String authority;
    private transient String userInfo;
    private transient String host;
    private transient int port = -1;
    private transient String path;
    private transient String query;
    private volatile transient String schemeSpecificPart;
    private volatile transient int hash;
    private volatile transient String decodedUserInfo = null;
    private volatile transient String decodedAuthority = null;
    private volatile transient String decodedPath = null;
    private volatile transient String decodedQuery = null;
    private volatile transient String decodedFragment = null;
    private volatile transient String decodedSchemeSpecificPart = null;
    private volatile String string;
    
    private URI() {
        
    }
    
    public URI(String str) throws URISyntaxException {
        
        new URI$Parser(this, str).parse(false);
    }
    
    public URI(String scheme, String userInfo, String host, int port, String path, String query, String fragment) throws URISyntaxException {
        
        String s = toString(scheme, null, null, userInfo, host, port, path, query, fragment);
        checkPath(s, scheme, path);
        new URI$Parser(this, s).parse(true);
    }
    
    public URI(String scheme, String authority, String path, String query, String fragment) throws URISyntaxException {
        
        String s = toString(scheme, null, authority, null, null, -1, path, query, fragment);
        checkPath(s, scheme, path);
        new URI$Parser(this, s).parse(false);
    }
    
    public URI(String scheme, String host, String path, String fragment) throws URISyntaxException {
        this(scheme, null, host, -1, path, null, fragment);
    }
    
    public URI(String scheme, String ssp, String fragment) throws URISyntaxException {
        
        new URI$Parser(this, toString(scheme, ssp, null, null, null, -1, null, null, fragment)).parse(false);
    }
    
    public static URI create(String str) {
        try {
            return new URI(str);
        } catch (URISyntaxException x) {
            IllegalArgumentException y = new IllegalArgumentException();
            y.initCause(x);
            throw y;
        }
    }
    
    public URI parseServerAuthority() throws URISyntaxException {
        if ((host != null) || (authority == null)) return this;
        defineString();
        new URI$Parser(this, string).parse(true);
        return this;
    }
    
    public URI normalize() {
        return normalize(this);
    }
    
    public URI resolve(URI uri) {
        return resolve(this, uri);
    }
    
    public URI resolve(String str) {
        return resolve(URI.create(str));
    }
    
    public URI relativize(URI uri) {
        return relativize(this, uri);
    }
    
    public URL toURL() throws MalformedURLException {
        if (!isAbsolute()) throw new IllegalArgumentException("URI is not absolute");
        return new URL(toString());
    }
    
    public String getScheme() {
        return scheme;
    }
    
    public boolean isAbsolute() {
        return scheme != null;
    }
    
    public boolean isOpaque() {
        return path == null;
    }
    
    public String getRawSchemeSpecificPart() {
        defineSchemeSpecificPart();
        return schemeSpecificPart;
    }
    
    public String getSchemeSpecificPart() {
        if (decodedSchemeSpecificPart == null) decodedSchemeSpecificPart = decode(getRawSchemeSpecificPart());
        return decodedSchemeSpecificPart;
    }
    
    public String getRawAuthority() {
        return authority;
    }
    
    public String getAuthority() {
        if (decodedAuthority == null) decodedAuthority = decode(authority);
        return decodedAuthority;
    }
    
    public String getRawUserInfo() {
        return userInfo;
    }
    
    public String getUserInfo() {
        if ((decodedUserInfo == null) && (userInfo != null)) decodedUserInfo = decode(userInfo);
        return decodedUserInfo;
    }
    
    public String getHost() {
        return host;
    }
    
    public int getPort() {
        return port;
    }
    
    public String getRawPath() {
        return path;
    }
    
    public String getPath() {
        if ((decodedPath == null) && (path != null)) decodedPath = decode(path);
        return decodedPath;
    }
    
    public String getRawQuery() {
        return query;
    }
    
    public String getQuery() {
        if ((decodedQuery == null) && (query != null)) decodedQuery = decode(query);
        return decodedQuery;
    }
    
    public String getRawFragment() {
        return fragment;
    }
    
    public String getFragment() {
        if ((decodedFragment == null) && (fragment != null)) decodedFragment = decode(fragment);
        return decodedFragment;
    }
    
    public boolean equals(Object ob) {
        if (ob == this) return true;
        if (!(ob instanceof URI)) return false;
        URI that = (URI)(URI)ob;
        if (this.isOpaque() != that.isOpaque()) return false;
        if (!equalIgnoringCase(this.scheme, that.scheme)) return false;
        if (!equal(this.fragment, that.fragment)) return false;
        if (this.isOpaque()) return equal(this.schemeSpecificPart, that.schemeSpecificPart);
        if (!equal(this.path, that.path)) return false;
        if (!equal(this.query, that.query)) return false;
        if (this.authority == that.authority) return true;
        if (this.host != null) {
            if (!equal(this.userInfo, that.userInfo)) return false;
            if (!equalIgnoringCase(this.host, that.host)) return false;
            if (this.port != that.port) return false;
        } else if (this.authority != null) {
            if (!equal(this.authority, that.authority)) return false;
        } else if (this.authority != that.authority) {
            return false;
        }
        return true;
    }
    
    public int hashCode() {
        if (hash != 0) return hash;
        int h = hashIgnoringCase(0, scheme);
        h = hash(h, fragment);
        if (isOpaque()) {
            h = hash(h, schemeSpecificPart);
        } else {
            h = hash(h, path);
            h = hash(h, query);
            if (host != null) {
                h = hash(h, userInfo);
                h = hashIgnoringCase(h, host);
                h += 1949 * port;
            } else {
                h = hash(h, authority);
            }
        }
        hash = h;
        return h;
    }
    
    public int compareTo(URI that) {
        int c;
        if ((c = compareIgnoringCase(this.scheme, that.scheme)) != 0) return c;
        if (this.isOpaque()) {
            if (that.isOpaque()) {
                if ((c = compare(this.schemeSpecificPart, that.schemeSpecificPart)) != 0) return c;
                return compare(this.fragment, that.fragment);
            }
            return +1;
        } else if (that.isOpaque()) {
            return -1;
        }
        if ((this.host != null) && (that.host != null)) {
            if ((c = compare(this.userInfo, that.userInfo)) != 0) return c;
            if ((c = compareIgnoringCase(this.host, that.host)) != 0) return c;
            if ((c = this.port - that.port) != 0) return c;
        } else {
            if ((c = compare(this.authority, that.authority)) != 0) return c;
        }
        if ((c = compare(this.path, that.path)) != 0) return c;
        if ((c = compare(this.query, that.query)) != 0) return c;
        return compare(this.fragment, that.fragment);
    }
    
    public String toString() {
        defineString();
        return string;
    }
    
    public String toASCIIString() {
        defineString();
        return encode(string);
    }
    
    private void writeObject(ObjectOutputStream os) throws IOException {
        defineString();
        os.defaultWriteObject();
    }
    
    private void readObject(ObjectInputStream is) throws ClassNotFoundException, IOException {
        port = -1;
        is.defaultReadObject();
        try {
            new URI$Parser(this, string).parse(false);
        } catch (URISyntaxException x) {
            IOException y = new InvalidObjectException("Invalid URI");
            y.initCause(x);
            throw y;
        }
    }
    
    private static int toLower(char c) {
        if ((c >= 'A') && (c <= 'Z')) return c + ('a' - 'A');
        return c;
    }
    
    private static boolean equal(String s, String t) {
        if (s == t) return true;
        if ((s != null) && (t != null)) {
            if (s.length() != t.length()) return false;
            if (s.indexOf('%') < 0) return s.equals(t);
            int n = s.length();
            for (int i = 0; i < n; ) {
                char c = s.charAt(i);
                char d = t.charAt(i);
                if (c != '%') {
                    if (c != d) return false;
                    i++;
                    continue;
                }
                i++;
                if (toLower(s.charAt(i)) != toLower(t.charAt(i))) return false;
                i++;
                if (toLower(s.charAt(i)) != toLower(t.charAt(i))) return false;
                i++;
            }
            return true;
        }
        return false;
    }
    
    private static boolean equalIgnoringCase(String s, String t) {
        if (s == t) return true;
        if ((s != null) && (t != null)) {
            int n = s.length();
            if (t.length() != n) return false;
            for (int i = 0; i < n; i++) {
                if (toLower(s.charAt(i)) != toLower(t.charAt(i))) return false;
            }
            return true;
        }
        return false;
    }
    
    private static int hash(int hash, String s) {
        if (s == null) return hash;
        return hash * 127 + s.hashCode();
    }
    
    private static int hashIgnoringCase(int hash, String s) {
        if (s == null) return hash;
        int h = hash;
        int n = s.length();
        for (int i = 0; i < n; i++) h = 31 * h + toLower(s.charAt(i));
        return h;
    }
    
    private static int compare(String s, String t) {
        if (s == t) return 0;
        if (s != null) {
            if (t != null) return s.compareTo(t); else return +1;
        } else {
            return -1;
        }
    }
    
    private static int compareIgnoringCase(String s, String t) {
        if (s == t) return 0;
        if (s != null) {
            if (t != null) {
                int sn = s.length();
                int tn = t.length();
                int n = sn < tn ? sn : tn;
                for (int i = 0; i < n; i++) {
                    int c = toLower(s.charAt(i)) - toLower(t.charAt(i));
                    if (c != 0) return c;
                }
                return sn - tn;
            }
            return +1;
        } else {
            return -1;
        }
    }
    
    private static void checkPath(String s, String scheme, String path) throws URISyntaxException {
        if (scheme != null) {
            if ((path != null) && ((path.length() > 0) && (path.charAt(0) != '/'))) throw new URISyntaxException(s, "Relative path in absolute URI");
        }
    }
    
    private void appendAuthority(StringBuffer sb, String authority, String userInfo, String host, int port) {
        if (host != null) {
            sb.append("//");
            if (userInfo != null) {
                sb.append(quote(userInfo, L_USERINFO, H_USERINFO));
                sb.append('@');
            }
            boolean needBrackets = ((host.indexOf(':') >= 0) && !host.startsWith("[") && !host.endsWith("]"));
            if (needBrackets) sb.append('[');
            sb.append(host);
            if (needBrackets) sb.append(']');
            if (port != -1) {
                sb.append(':');
                sb.append(port);
            }
        } else if (authority != null) {
            sb.append("//");
            if (authority.startsWith("[")) {
                int end = authority.indexOf("]");
                if (end != -1 && authority.indexOf(":") != -1) {
                    String doquote;
                    String dontquote;
                    if (end == authority.length()) {
                        dontquote = authority;
                        doquote = "";
                    } else {
                        dontquote = authority.substring(0, end + 1);
                        doquote = authority.substring(end + 1);
                    }
                    sb.append(dontquote);
                    sb.append(quote(doquote, L_REG_NAME | L_SERVER, H_REG_NAME | H_SERVER));
                }
            } else {
                sb.append(quote(authority, L_REG_NAME | L_SERVER, H_REG_NAME | H_SERVER));
            }
        }
    }
    
    private void appendSchemeSpecificPart(StringBuffer sb, String opaquePart, String authority, String userInfo, String host, int port, String path, String query) {
        if (opaquePart != null) {
            if (opaquePart.startsWith("//[")) {
                int end = opaquePart.indexOf("]");
                if (end != -1 && opaquePart.indexOf(":") != -1) {
                    String doquote;
                    String dontquote;
                    if (end == opaquePart.length()) {
                        dontquote = opaquePart;
                        doquote = "";
                    } else {
                        dontquote = opaquePart.substring(0, end + 1);
                        doquote = opaquePart.substring(end + 1);
                    }
                    sb.append(dontquote);
                    sb.append(quote(doquote, L_URIC, H_URIC));
                }
            } else {
                sb.append(quote(opaquePart, L_URIC, H_URIC));
            }
        } else {
            appendAuthority(sb, authority, userInfo, host, port);
            if (path != null) sb.append(quote(path, L_PATH, H_PATH));
            if (query != null) {
                sb.append('?');
                sb.append(quote(query, L_URIC, H_URIC));
            }
        }
    }
    
    private void appendFragment(StringBuffer sb, String fragment) {
        if (fragment != null) {
            sb.append('#');
            sb.append(quote(fragment, L_URIC, H_URIC));
        }
    }
    
    private String toString(String scheme, String opaquePart, String authority, String userInfo, String host, int port, String path, String query, String fragment) {
        StringBuffer sb = new StringBuffer();
        if (scheme != null) {
            sb.append(scheme);
            sb.append(':');
        }
        appendSchemeSpecificPart(sb, opaquePart, authority, userInfo, host, port, path, query);
        appendFragment(sb, fragment);
        return sb.toString();
    }
    
    private void defineSchemeSpecificPart() {
        if (schemeSpecificPart != null) return;
        StringBuffer sb = new StringBuffer();
        appendSchemeSpecificPart(sb, null, getAuthority(), getUserInfo(), host, port, getPath(), getQuery());
        if (sb.length() == 0) return;
        schemeSpecificPart = sb.toString();
    }
    
    private void defineString() {
        if (string != null) return;
        StringBuffer sb = new StringBuffer();
        if (scheme != null) {
            sb.append(scheme);
            sb.append(':');
        }
        if (isOpaque()) {
            sb.append(schemeSpecificPart);
        } else {
            if (host != null) {
                sb.append("//");
                if (userInfo != null) {
                    sb.append(userInfo);
                    sb.append('@');
                }
                boolean needBrackets = ((host.indexOf(':') >= 0) && !host.startsWith("[") && !host.endsWith("]"));
                if (needBrackets) sb.append('[');
                sb.append(host);
                if (needBrackets) sb.append(']');
                if (port != -1) {
                    sb.append(':');
                    sb.append(port);
                }
            } else if (authority != null) {
                sb.append("//");
                sb.append(authority);
            }
            if (path != null) sb.append(path);
            if (query != null) {
                sb.append('?');
                sb.append(query);
            }
        }
        if (fragment != null) {
            sb.append('#');
            sb.append(fragment);
        }
        string = sb.toString();
    }
    
    private static String resolvePath(String base, String child, boolean absolute) {
        int i = base.lastIndexOf('/');
        int cn = child.length();
        String path = "";
        if (cn == 0) {
            if (i >= 0) path = base.substring(0, i + 1);
        } else {
            StringBuffer sb = new StringBuffer(base.length() + cn);
            if (i >= 0) sb.append(base.substring(0, i + 1));
            sb.append(child);
            path = sb.toString();
        }
        String np = normalize(path);
        return np;
    }
    
    private static URI resolve(URI base, URI child) {
        if (child.isOpaque() || base.isOpaque()) return child;
        if ((child.scheme == null) && (child.authority == null) && child.path.equals("") && (child.fragment != null) && (child.query == null)) {
            if ((base.fragment != null) && child.fragment.equals(base.fragment)) {
                return base;
            }
            URI ru = new URI();
            ru.scheme = base.scheme;
            ru.authority = base.authority;
            ru.userInfo = base.userInfo;
            ru.host = base.host;
            ru.port = base.port;
            ru.path = base.path;
            ru.fragment = child.fragment;
            ru.query = base.query;
            return ru;
        }
        if (child.scheme != null) return child;
        URI ru = new URI();
        ru.scheme = base.scheme;
        ru.query = child.query;
        ru.fragment = child.fragment;
        if (child.authority == null) {
            ru.authority = base.authority;
            ru.host = base.host;
            ru.userInfo = base.userInfo;
            ru.port = base.port;
            String cp = (child.path == null) ? "" : child.path;
            if ((cp.length() > 0) && (cp.charAt(0) == '/')) {
                ru.path = child.path;
            } else {
                ru.path = resolvePath(base.path, cp, base.isAbsolute());
            }
        } else {
            ru.authority = child.authority;
            ru.host = child.host;
            ru.userInfo = child.userInfo;
            ru.host = child.host;
            ru.port = child.port;
            ru.path = child.path;
        }
        return ru;
    }
    
    private static URI normalize(URI u) {
        if (u.isOpaque() || (u.path == null) || (u.path.length() == 0)) return u;
        String np = normalize(u.path);
        if (np == u.path) return u;
        URI v = new URI();
        v.scheme = u.scheme;
        v.fragment = u.fragment;
        v.authority = u.authority;
        v.userInfo = u.userInfo;
        v.host = u.host;
        v.port = u.port;
        v.path = np;
        v.query = u.query;
        return v;
    }
    
    private static URI relativize(URI base, URI child) {
        if (child.isOpaque() || base.isOpaque()) return child;
        if (!equalIgnoringCase(base.scheme, child.scheme) || !equal(base.authority, child.authority)) return child;
        String bp = normalize(base.path);
        String cp = normalize(child.path);
        if (!bp.equals(cp)) {
            if (!bp.endsWith("/")) bp = bp + "/";
            if (!cp.startsWith(bp)) return child;
        }
        URI v = new URI();
        v.path = cp.substring(bp.length());
        v.query = child.query;
        v.fragment = child.fragment;
        return v;
    }
    
    private static int needsNormalization(String path) {
        boolean normal = true;
        int ns = 0;
        int end = path.length() - 1;
        int p = 0;
        while (p <= end) {
            if (path.charAt(p) != '/') break;
            p++;
        }
        if (p > 1) normal = false;
        while (p <= end) {
            if ((path.charAt(p) == '.') && ((p == end) || ((path.charAt(p + 1) == '/') || ((path.charAt(p + 1) == '.') && ((p + 1 == end) || (path.charAt(p + 2) == '/')))))) {
                normal = false;
            }
            ns++;
            while (p <= end) {
                if (path.charAt(p++) != '/') continue;
                while (p <= end) {
                    if (path.charAt(p) != '/') break;
                    normal = false;
                    p++;
                }
                break;
            }
        }
        return normal ? -1 : ns;
    }
    
    private static void split(char[] path, int[] segs) {
        int end = path.length - 1;
        int p = 0;
        int i = 0;
        while (p <= end) {
            if (path[p] != '/') break;
            path[p] = '\000';
            p++;
        }
        while (p <= end) {
            segs[i++] = p++;
            while (p <= end) {
                if (path[p++] != '/') continue;
                path[p - 1] = '\000';
                while (p <= end) {
                    if (path[p] != '/') break;
                    path[p++] = '\000';
                }
                break;
            }
        }
        if (i != segs.length) throw new InternalError();
    }
    
    private static int join(char[] path, int[] segs) {
        int ns = segs.length;
        int end = path.length - 1;
        int p = 0;
        if (path[p] == '\000') {
            path[p++] = '/';
        }
        for (int i = 0; i < ns; i++) {
            int q = segs[i];
            if (q == -1) continue;
            if (p == q) {
                while ((p <= end) && (path[p] != '\000')) p++;
                if (p <= end) {
                    path[p++] = '/';
                }
            } else if (p < q) {
                while ((q <= end) && (path[q] != '\000')) path[p++] = path[q++];
                if (q <= end) {
                    path[p++] = '/';
                }
            } else throw new InternalError();
        }
        return p;
    }
    
    private static void removeDots(char[] path, int[] segs) {
        int ns = segs.length;
        int end = path.length - 1;
        for (int i = 0; i < ns; i++) {
            int dots = 0;
            do {
                int p = segs[i];
                if (path[p] == '.') {
                    if (p == end) {
                        dots = 1;
                        break;
                    } else if (path[p + 1] == '\000') {
                        dots = 1;
                        break;
                    } else if ((path[p + 1] == '.') && ((p + 1 == end) || (path[p + 2] == '\000'))) {
                        dots = 2;
                        break;
                    }
                }
                i++;
            }             while (i < ns);
            if ((i > ns) || (dots == 0)) break;
            if (dots == 1) {
                segs[i] = -1;
            } else {
                int j;
                for (j = i - 1; j >= 0; j--) {
                    if (segs[j] != -1) break;
                }
                if (j >= 0) {
                    int q = segs[j];
                    if (!((path[q] == '.') && (path[q + 1] == '.') && (path[q + 2] == '\000'))) {
                        segs[i] = -1;
                        segs[j] = -1;
                    }
                }
            }
        }
    }
    
    private static void maybeAddLeadingDot(char[] path, int[] segs) {
        if (path[0] == '\000') return;
        int ns = segs.length;
        int f = 0;
        while (f < ns) {
            if (segs[f] >= 0) break;
            f++;
        }
        if ((f >= ns) || (f == 0)) return;
        int p = segs[f];
        while ((p < path.length) && (path[p] != ':') && (path[p] != '\000')) p++;
        if (p >= path.length || path[p] == '\000') return;
        path[0] = '.';
        path[1] = '\000';
        segs[0] = 0;
    }
    
    private static String normalize(String ps) {
        int ns = needsNormalization(ps);
        if (ns < 0) return ps;
        char[] path = ps.toCharArray();
        int[] segs = new int[ns];
        split(path, segs);
        removeDots(path, segs);
        maybeAddLeadingDot(path, segs);
        String s = new String(path, 0, join(path, segs));
        if (s.equals(ps)) {
            return ps;
        }
        return s;
    }
    
    private static long lowMask(String chars) {
        int n = chars.length();
        long m = 0;
        for (int i = 0; i < n; i++) {
            char c = chars.charAt(i);
            if (c < 64) m |= (1L << c);
        }
        return m;
    }
    
    private static long highMask(String chars) {
        int n = chars.length();
        long m = 0;
        for (int i = 0; i < n; i++) {
            char c = chars.charAt(i);
            if ((c >= 64) && (c < 128)) m |= (1L << (c - 64));
        }
        return m;
    }
    
    private static long lowMask(char first, char last) {
        long m = 0;
        int f = Math.max(Math.min(first, 63), 0);
        int l = Math.max(Math.min(last, 63), 0);
        for (int i = f; i <= l; i++) m |= 1L << i;
        return m;
    }
    
    private static long highMask(char first, char last) {
        long m = 0;
        int f = Math.max(Math.min(first, 127), 64) - 64;
        int l = Math.max(Math.min(last, 127), 64) - 64;
        for (int i = f; i <= l; i++) m |= 1L << i;
        return m;
    }
    
    private static boolean match(char c, long lowMask, long highMask) {
        if (c < 64) return ((1L << c) & lowMask) != 0;
        if (c < 128) return ((1L << (c - 64)) & highMask) != 0;
        return false;
    }
    private static final long L_DIGIT = lowMask('0', '9');
    private static final long H_DIGIT = 0L;
    private static final long L_UPALPHA = 0L;
    private static final long H_UPALPHA = highMask('A', 'Z');
    private static final long L_LOWALPHA = 0L;
    private static final long H_LOWALPHA = highMask('a', 'z');
    private static final long L_ALPHA = L_LOWALPHA | L_UPALPHA;
    private static final long H_ALPHA = H_LOWALPHA | H_UPALPHA;
    private static final long L_ALPHANUM = L_DIGIT | L_ALPHA;
    private static final long H_ALPHANUM = H_DIGIT | H_ALPHA;
    private static final long L_HEX = L_DIGIT;
    private static final long H_HEX = highMask('A', 'F') | highMask('a', 'f');
    private static final long L_MARK = lowMask("-_.!~*\'()");
    private static final long H_MARK = highMask("-_.!~*\'()");
    private static final long L_UNRESERVED = L_ALPHANUM | L_MARK;
    private static final long H_UNRESERVED = H_ALPHANUM | H_MARK;
    private static final long L_RESERVED = lowMask(";/?:@&=+$,[]");
    private static final long H_RESERVED = highMask(";/?:@&=+$,[]");
    private static final long L_ESCAPED = 1L;
    private static final long H_ESCAPED = 0L;
    private static final long L_URIC = L_RESERVED | L_UNRESERVED | L_ESCAPED;
    private static final long H_URIC = H_RESERVED | H_UNRESERVED | H_ESCAPED;
    private static final long L_PCHAR = L_UNRESERVED | L_ESCAPED | lowMask(":@&=+$,");
    private static final long H_PCHAR = H_UNRESERVED | H_ESCAPED | highMask(":@&=+$,");
    private static final long L_PATH = L_PCHAR | lowMask(";/");
    private static final long H_PATH = H_PCHAR | highMask(";/");
    private static final long L_DASH = lowMask("-");
    private static final long H_DASH = highMask("-");
    private static final long L_DOT = lowMask(".");
    private static final long H_DOT = highMask(".");
    private static final long L_USERINFO = L_UNRESERVED | L_ESCAPED | lowMask(";:&=+$,");
    private static final long H_USERINFO = H_UNRESERVED | H_ESCAPED | highMask(";:&=+$,");
    private static final long L_REG_NAME = L_UNRESERVED | L_ESCAPED | lowMask("$,;:@&=+");
    private static final long H_REG_NAME = H_UNRESERVED | H_ESCAPED | highMask("$,;:@&=+");
    private static final long L_SERVER = L_USERINFO | L_ALPHANUM | L_DASH | lowMask(".:@[]");
    private static final long H_SERVER = H_USERINFO | H_ALPHANUM | H_DASH | highMask(".:@[]");
    private static final long L_SERVER_PERCENT = L_SERVER | lowMask("%");
    private static final long H_SERVER_PERCENT = H_SERVER | highMask("%");
    private static final long L_LEFT_BRACKET = lowMask("[");
    private static final long H_LEFT_BRACKET = highMask("[");
    private static final long L_SCHEME = L_ALPHA | L_DIGIT | lowMask("+-.");
    private static final long H_SCHEME = H_ALPHA | H_DIGIT | highMask("+-.");
    private static final long L_URIC_NO_SLASH = L_UNRESERVED | L_ESCAPED | lowMask(";?:@&=+$,");
    private static final long H_URIC_NO_SLASH = H_UNRESERVED | H_ESCAPED | highMask(";?:@&=+$,");
    private static final char[] hexDigits = {'0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'};
    
    private static void appendEscape(StringBuffer sb, byte b) {
        sb.append('%');
        sb.append(hexDigits[(b >> 4) & 15]);
        sb.append(hexDigits[(b >> 0) & 15]);
    }
    
    private static void appendEncoded(StringBuffer sb, char c) {
        ByteBuffer bb = null;
        try {
            bb = ThreadLocalCoders.encoderFor("UTF-8").encode(CharBuffer.wrap("" + c));
        } catch (CharacterCodingException x) {
            if (!$assertionsDisabled) throw new AssertionError();
        }
        while (bb.hasRemaining()) {
            int b = bb.get() & 255;
            if (b >= 128) appendEscape(sb, (byte)b); else sb.append((char)b);
        }
    }
    
    private static String quote(String s, long lowMask, long highMask) {
        int n = s.length();
        StringBuffer sb = null;
        boolean allowNonASCII = ((lowMask & L_ESCAPED) != 0);
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c < '\200') {
                if (!match(c, lowMask, highMask)) {
                    if (sb == null) {
                        sb = new StringBuffer();
                        sb.append(s.substring(0, i));
                    }
                    appendEscape(sb, (byte)c);
                } else {
                    if (sb != null) sb.append(c);
                }
            } else if (allowNonASCII && (Character.isSpaceChar(c) || Character.isISOControl(c))) {
                if (sb == null) {
                    sb = new StringBuffer();
                    sb.append(s.substring(0, i));
                }
                appendEncoded(sb, c);
            } else {
                if (sb != null) sb.append(c);
            }
        }
        return (sb == null) ? s : sb.toString();
    }
    
    private static String encode(String s) {
        int n = s.length();
        if (n == 0) return s;
        for (int i = 0; ; ) {
            if (s.charAt(i) >= '\200') break;
            if (++i >= n) return s;
        }
        String ns = Normalizer.normalize(s, Normalizer.COMPOSE, 0);
        ByteBuffer bb = null;
        try {
            bb = ThreadLocalCoders.encoderFor("UTF-8").encode(CharBuffer.wrap(ns));
        } catch (CharacterCodingException x) {
            if (!$assertionsDisabled) throw new AssertionError();
        }
        StringBuffer sb = new StringBuffer();
        while (bb.hasRemaining()) {
            int b = bb.get() & 255;
            if (b >= 128) appendEscape(sb, (byte)b); else sb.append((char)b);
        }
        return sb.toString();
    }
    
    private static int decode(char c) {
        if ((c >= '0') && (c <= '9')) return c - '0';
        if ((c >= 'a') && (c <= 'f')) return c - 'a' + 10;
        if ((c >= 'A') && (c <= 'F')) return c - 'A' + 10;
        if (!$assertionsDisabled) throw new AssertionError();
        return -1;
    }
    
    private static byte decode(char c1, char c2) {
        return (byte)(((decode(c1) & 15) << 4) | ((decode(c2) & 15) << 0));
    }
    
    private static String decode(String s) {
        if (s == null) return s;
        int n = s.length();
        if (n == 0) return s;
        if (s.indexOf('%') < 0) return s;
        byte[] ba = new byte[n];
        StringBuffer sb = new StringBuffer(n);
        ByteBuffer bb = ByteBuffer.allocate(n);
        CharBuffer cb = CharBuffer.allocate(n);
        CharsetDecoder dec = ThreadLocalCoders.decoderFor("UTF-8").onMalformedInput(CodingErrorAction.REPLACE).onUnmappableCharacter(CodingErrorAction.REPLACE);
        char c = s.charAt(0);
        boolean betweenBrackets = false;
        for (int i = 0; i < n; ) {
            if (!$assertionsDisabled && !(c == s.charAt(i))) throw new AssertionError();
            if (c == '[') {
                betweenBrackets = true;
            } else if (betweenBrackets && c == ']') {
                betweenBrackets = false;
            }
            if (c != '%' || betweenBrackets) {
                sb.append(c);
                if (++i >= n) break;
                c = s.charAt(i);
                continue;
            }
            bb.clear();
            int ui = i;
            for (; ; ) {
                if (!$assertionsDisabled && !(n - i >= 2)) throw new AssertionError();
                bb.put(decode(s.charAt(++i), s.charAt(++i)));
                if (++i >= n) break;
                c = s.charAt(i);
                if (c != '%') break;
            }
            bb.flip();
            cb.clear();
            dec.reset();
            CoderResult cr = dec.decode(bb, cb, true);
            if (!$assertionsDisabled && !cr.isUnderflow()) throw new AssertionError();
            cr = dec.flush(cb);
            if (!$assertionsDisabled && !cr.isUnderflow()) throw new AssertionError();
            sb.append(cb.flip().toString());
        }
        return sb.toString();
    }
    {
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((URI)x0);
    }
}
