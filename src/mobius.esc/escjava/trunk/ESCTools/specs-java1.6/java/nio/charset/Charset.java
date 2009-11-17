package java.nio.charset;

import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.spi.CharsetProvider;
import java.security.AccessController;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import sun.nio.cs.StandardCharsets;
import sun.nio.cs.ThreadLocalCoders;
import sun.security.action.GetPropertyAction;

public abstract class Charset implements Comparable {
    
    /*synthetic*/ static void access$300(Iterator x0, Map x1) {
        put(x0, x1);
    }
    
    /*synthetic*/ static CharsetProvider access$200() {
        return standardProvider;
    }
    
    /*synthetic*/ static CharsetProvider access$102(CharsetProvider x0) {
        return extendedProvider = x0;
    }
    
    /*synthetic*/ static Iterator access$000() {
        return providers();
    }
    private static volatile String bugLevel = null;
    
    static boolean atBugLevel(String bl) {
        if (bugLevel == null) {
            if (!sun.misc.VM.isBooted()) return false;
            java.security.PrivilegedAction pa = new GetPropertyAction("sun.nio.cs.bugLevel");
            String value = (String)(String)AccessController.doPrivileged(pa);
            bugLevel = (value != null) ? value : "";
        }
        return bugLevel.equals(bl);
    }
    
    private static void checkName(String s) {
        int n = s.length();
        if (!atBugLevel("1.4")) {
            if (n == 0) throw new IllegalCharsetNameException(s);
        }
        for (int i = 0; i < n; i++) {
            char c = s.charAt(i);
            if (c >= 'A' && c <= 'Z') continue;
            if (c >= 'a' && c <= 'z') continue;
            if (c >= '0' && c <= '9') continue;
            if (c == '-') continue;
            if (c == ':') continue;
            if (c == '_') continue;
            if (c == '.') continue;
            throw new IllegalCharsetNameException(s);
        }
    }
    private static CharsetProvider standardProvider = new StandardCharsets();
    private static volatile Object[] cache1 = null;
    private static volatile Object[] cache2 = null;
    
    private static void cache(String charsetName, Charset cs) {
        cache2 = cache1;
        cache1 = new Object[]{charsetName, cs};
    }
    
    private static Iterator providers() {
        return new Charset$1();
    }
    private static ThreadLocal gate = new ThreadLocal();
    
    private static Charset lookupViaProviders(final String charsetName) {
        if (!sun.misc.VM.isBooted()) return null;
        if (gate.get() != null) return null;
        try {
            gate.set(gate);
            return (Charset)(Charset)AccessController.doPrivileged(new Charset$2(charsetName));
        } finally {
            gate.set(null);
        }
    }
    private static Object extendedProviderLock = new Object();
    private static boolean extendedProviderProbed = false;
    private static CharsetProvider extendedProvider = null;
    
    private static void probeExtendedProvider() {
        AccessController.doPrivileged(new Charset$3());
    }
    
    private static Charset lookupExtendedCharset(String charsetName) {
        CharsetProvider ecp = null;
        synchronized (extendedProviderLock) {
            if (!extendedProviderProbed) {
                probeExtendedProvider();
                extendedProviderProbed = true;
            }
            ecp = extendedProvider;
        }
        return (ecp != null) ? ecp.charsetForName(charsetName) : null;
    }
    
    private static Charset lookup(String charsetName) {
        if (charsetName == null) throw new IllegalArgumentException("Null charset name");
        Object[] a;
        if ((a = cache1) != null && charsetName.equals(a[0])) return (Charset)(Charset)a[1];
        return lookup2(charsetName);
    }
    
    private static Charset lookup2(String charsetName) {
        Object[] a;
        if ((a = cache2) != null && charsetName.equals(a[0])) {
            cache2 = cache1;
            cache1 = a;
            return (Charset)(Charset)a[1];
        }
        Charset cs;
        if ((cs = standardProvider.charsetForName(charsetName)) != null || (cs = lookupExtendedCharset(charsetName)) != null || (cs = lookupViaProviders(charsetName)) != null) {
            cache(charsetName, cs);
            return cs;
        }
        checkName(charsetName);
        return null;
    }
    
    public static boolean isSupported(String charsetName) {
        return (lookup(charsetName) != null);
    }
    
    public static Charset forName(String charsetName) {
        Charset cs = lookup(charsetName);
        if (cs != null) return cs;
        throw new UnsupportedCharsetException(charsetName);
    }
    
    private static void put(Iterator i, Map m) {
        while (i.hasNext()) {
            Charset cs = (Charset)(Charset)i.next();
            if (!m.containsKey(cs.name())) m.put(cs.name(), cs);
        }
    }
    
    public static SortedMap availableCharsets() {
        return (SortedMap)(SortedMap)AccessController.doPrivileged(new Charset$4());
    }
    private static Charset defaultCharset;
    
    public static Charset defaultCharset() {
        synchronized (Charset.class) {
            if (defaultCharset == null) {
                java.security.PrivilegedAction pa = new GetPropertyAction("file.encoding");
                String csn = (String)(String)AccessController.doPrivileged(pa);
                Charset cs = lookup(csn);
                if (cs != null) return cs;
                return forName("UTF-8");
            }
            return defaultCharset;
        }
    }
    private final String name;
    private final String[] aliases;
    private Set aliasSet = null;
    
    protected Charset(String canonicalName, String[] aliases) {
        
        checkName(canonicalName);
        String[] as = (aliases == null) ? new String[0] : aliases;
        for (int i = 0; i < as.length; i++) checkName(as[i]);
        this.name = canonicalName;
        this.aliases = as;
    }
    
    public final String name() {
        return name;
    }
    
    public final Set aliases() {
        if (aliasSet != null) return aliasSet;
        int n = aliases.length;
        HashSet hs = new HashSet(n);
        for (int i = 0; i < n; i++) hs.add(aliases[i]);
        aliasSet = Collections.unmodifiableSet(hs);
        return aliasSet;
    }
    
    public String displayName() {
        return name;
    }
    
    public final boolean isRegistered() {
        return !name.startsWith("X-") && !name.startsWith("x-");
    }
    
    public String displayName(Locale locale) {
        return name;
    }
    
    public abstract boolean contains(Charset cs);
    
    public abstract CharsetDecoder newDecoder();
    
    public abstract CharsetEncoder newEncoder();
    
    public boolean canEncode() {
        return true;
    }
    
    public final CharBuffer decode(ByteBuffer bb) {
        try {
            return ThreadLocalCoders.decoderFor(this).onMalformedInput(CodingErrorAction.REPLACE).onUnmappableCharacter(CodingErrorAction.REPLACE).decode(bb);
        } catch (CharacterCodingException x) {
            throw new Error(x);
        }
    }
    
    public final ByteBuffer encode(CharBuffer cb) {
        try {
            return ThreadLocalCoders.encoderFor(this).onMalformedInput(CodingErrorAction.REPLACE).onUnmappableCharacter(CodingErrorAction.REPLACE).encode(cb);
        } catch (CharacterCodingException x) {
            throw new Error(x);
        }
    }
    
    public final ByteBuffer encode(String str) {
        return encode(CharBuffer.wrap(str));
    }
    
    public final int compareTo(Charset that) {
        return (name().compareToIgnoreCase(that.name()));
    }
    
    public final int hashCode() {
        return name().hashCode();
    }
    
    public final boolean equals(Object ob) {
        if (!(ob instanceof Charset)) return false;
        if (this == ob) return true;
        return name.equals(((Charset)(Charset)ob).name());
    }
    
    public final String toString() {
        return name();
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((Charset)x0);
    }
}
