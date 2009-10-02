package java.security;

import java.io.*;
import java.util.*;
import java.lang.ref.*;
import java.lang.reflect.*;

public abstract class Provider extends Properties {
    
    /*synthetic*/ static Map access$1000() {
        return knownEngines;
    }
    
    /*synthetic*/ static String access$900(String x0) {
        return getEngineName(x0);
    }
    {
    }
    static final long serialVersionUID = -4298000515446427739L;
    private static final sun.security.util.Debug debug = sun.security.util.Debug.getInstance("provider", "Provider");
    private String name;
    private String info;
    private double version;
    private transient Set entrySet = null;
    private transient int entrySetCallCount = 0;
    
    protected Provider(String name, double version, String info) {
        
        this.name = name;
        this.version = version;
        this.info = info;
        putId();
    }
    
    public String getName() {
        return name;
    }
    
    public double getVersion() {
        return version;
    }
    
    public String getInfo() {
        return info;
    }
    
    public String toString() {
        return name + " version " + version;
    }
    
    public synchronized void clear() {
        check("clearProviderProperties." + name);
        if (debug != null) {
            debug.println("Remove " + name + " provider properties");
        }
        implClear();
    }
    
    public synchronized void load(InputStream inStream) throws IOException {
        check("putProviderProperty." + name);
        if (debug != null) {
            debug.println("Load " + name + " provider properties");
        }
        Properties tempProperties = new Properties();
        tempProperties.load(inStream);
        implPutAll(tempProperties);
    }
    
    public synchronized void putAll(Map t) {
        check("putProviderProperty." + name);
        if (debug != null) {
            debug.println("Put all " + name + " provider properties");
        }
        implPutAll(t);
    }
    
    public synchronized Set entrySet() {
        if (entrySet == null) {
            if (entrySetCallCount++ == 0) entrySet = Collections.unmodifiableMap(this).entrySet(); else return super.entrySet();
        }
        if (entrySetCallCount != 2) throw new RuntimeException("Internal error.");
        return entrySet;
    }
    
    public Set keySet() {
        return Collections.unmodifiableSet(super.keySet());
    }
    
    public Collection values() {
        return Collections.unmodifiableCollection(super.values());
    }
    
    public synchronized Object put(Object key, Object value) {
        check("putProviderProperty." + name);
        if (debug != null) {
            debug.println("Set " + name + " provider property [" + key + "/" + value + "]");
        }
        return implPut(key, value);
    }
    
    public synchronized Object remove(Object key) {
        check("removeProviderProperty." + name);
        if (debug != null) {
            debug.println("Remove " + name + " provider property " + key);
        }
        return implRemove(key);
    }
    
    private static void check(String directive) {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkSecurityAccess(directive);
        }
    }
    private transient boolean legacyChanged;
    private transient boolean servicesChanged;
    private transient Map legacyStrings;
    private transient Map serviceMap;
    private transient Map legacyMap;
    private transient Set serviceSet;
    
    private void putId() {
        super.put("Provider.id name", String.valueOf(name));
        super.put("Provider.id version", String.valueOf(version));
        super.put("Provider.id info", String.valueOf(info));
        super.put("Provider.id className", this.getClass().getName());
    }
    
    private void implPutAll(Map t) {
        for (Iterator i$ = ((Map)t).entrySet().iterator(); i$.hasNext(); ) {
            Map$Entry e = (Map$Entry)i$.next();
            {
                implPut(e.getKey(), e.getValue());
            }
        }
    }
    
    private Object implRemove(Object key) {
        if (key instanceof String) {
            String keyString = (String)(String)key;
            if (keyString.startsWith("Provider.")) {
                return null;
            }
            legacyChanged = true;
            if (legacyStrings == null) {
                legacyStrings = new LinkedHashMap();
            }
            legacyStrings.remove(keyString);
        }
        return super.remove(key);
    }
    
    private Object implPut(Object key, Object value) {
        if ((key instanceof String) && (value instanceof String)) {
            String keyString = (String)(String)key;
            if (keyString.startsWith("Provider.")) {
                return null;
            }
            legacyChanged = true;
            if (legacyStrings == null) {
                legacyStrings = new LinkedHashMap();
            }
            legacyStrings.put(keyString, (String)(String)value);
        }
        return super.put(key, value);
    }
    
    private void implClear() {
        super.clear();
        putId();
        if (legacyStrings != null) {
            legacyStrings.clear();
        }
        if (legacyMap != null) {
            legacyMap.clear();
        }
        if (serviceMap != null) {
            serviceMap.clear();
        }
        legacyChanged = false;
        servicesChanged = false;
        serviceSet = null;
    }
    {
    }
    
    private void ensureLegacyParsed() {
        if ((legacyChanged == false) || (legacyStrings == null)) {
            return;
        }
        serviceSet = null;
        if (legacyMap == null) {
            legacyMap = new LinkedHashMap();
        } else {
            legacyMap.clear();
        }
        for (Iterator i$ = legacyStrings.entrySet().iterator(); i$.hasNext(); ) {
            Map$Entry entry = (Map$Entry)i$.next();
            {
                parseLegacyPut((String)entry.getKey(), (String)entry.getValue());
            }
        }
        removeInvalidServices(legacyMap);
        legacyChanged = false;
    }
    
    private void removeInvalidServices(Map map) {
        for (Iterator t = map.entrySet().iterator(); t.hasNext(); ) {
            Map$Entry entry = (Map$Entry)(Map$Entry)t.next();
            Provider$Service s = (Provider$Service)(Provider$Service)entry.getValue();
            if (Provider.Service.access$000(s) == false) {
                t.remove();
            }
        }
    }
    
    private String[] getTypeAndAlgorithm(String key) {
        int i = key.indexOf(".");
        if (i < 1) {
            if (debug != null) {
                debug.println("Ignoring invalid entry in provider " + name + ":" + key);
            }
            return null;
        }
        String type = key.substring(0, i);
        String alg = key.substring(i + 1);
        return new String[]{type, alg};
    }
    private static final String ALIAS_PREFIX = "Alg.Alias.";
    private static final String ALIAS_PREFIX_LOWER = "alg.alias.";
    private static final int ALIAS_LENGTH = ALIAS_PREFIX.length();
    
    private void parseLegacyPut(String name, String value) {
        if (name.toLowerCase(Locale.ENGLISH).startsWith(ALIAS_PREFIX_LOWER)) {
            String stdAlg = value;
            String aliasKey = name.substring(ALIAS_LENGTH);
            String[] typeAndAlg = getTypeAndAlgorithm(aliasKey);
            if (typeAndAlg == null) {
                return;
            }
            String type = getEngineName(typeAndAlg[0]);
            String aliasAlg = typeAndAlg[1].intern();
            Provider$ServiceKey key = new Provider$ServiceKey(type, stdAlg, true, null);
            Provider$Service s = (Provider$Service)(Provider$Service)legacyMap.get(key);
            if (s == null) {
                s = new Provider$Service(this, null);
                Provider.Service.access$302(s, type);
                Provider.Service.access$402(s, stdAlg);
                legacyMap.put(key, s);
            }
            legacyMap.put(new Provider$ServiceKey(type, aliasAlg, true, null), s);
            Provider.Service.access$500(s, aliasAlg);
        } else {
            String[] typeAndAlg = getTypeAndAlgorithm(name);
            if (typeAndAlg == null) {
                return;
            }
            int i = typeAndAlg[1].indexOf(' ');
            if (i == -1) {
                String type = getEngineName(typeAndAlg[0]);
                String stdAlg = typeAndAlg[1].intern();
                String className = value;
                Provider$ServiceKey key = new Provider$ServiceKey(type, stdAlg, true, null);
                Provider$Service s = (Provider$Service)(Provider$Service)legacyMap.get(key);
                if (s == null) {
                    s = new Provider$Service(this, null);
                    Provider.Service.access$302(s, type);
                    Provider.Service.access$402(s, stdAlg);
                    legacyMap.put(key, s);
                }
                Provider.Service.access$602(s, className);
            } else {
                String attributeValue = value;
                String type = getEngineName(typeAndAlg[0]);
                String attributeString = typeAndAlg[1];
                String stdAlg = attributeString.substring(0, i).intern();
                String attributeName = attributeString.substring(i + 1);
                while (attributeName.startsWith(" ")) {
                    attributeName = attributeName.substring(1);
                }
                attributeName = attributeName.intern();
                Provider$ServiceKey key = new Provider$ServiceKey(type, stdAlg, true, null);
                Provider$Service s = (Provider$Service)(Provider$Service)legacyMap.get(key);
                if (s == null) {
                    s = new Provider$Service(this, null);
                    Provider.Service.access$302(s, type);
                    Provider.Service.access$402(s, stdAlg);
                    legacyMap.put(key, s);
                }
                s.addAttribute(attributeName, attributeValue);
            }
        }
    }
    
    public synchronized Provider$Service getService(String type, String algorithm) {
        Provider$ServiceKey key = previousKey;
        if (key.matches(type, algorithm) == false) {
            key = new Provider$ServiceKey(type, algorithm, false, null);
            previousKey = key;
        }
        if (serviceMap != null) {
            Provider$Service service = (Provider$Service)serviceMap.get(key);
            if (service != null) {
                return service;
            }
        }
        ensureLegacyParsed();
        return (legacyMap != null) ? (Provider$Service)legacyMap.get(key) : null;
    }
    private static volatile Provider$ServiceKey previousKey = new Provider$ServiceKey("", "", false, null);
    
    public synchronized Set getServices() {
        if (legacyChanged || servicesChanged) {
            serviceSet = null;
        } else if (serviceSet != null) {
            return serviceSet;
        }
        ensureLegacyParsed();
        serviceSet = new LinkedHashSet();
        if (serviceMap != null) {
            serviceSet.addAll(serviceMap.values());
        }
        if (legacyMap != null) {
            serviceSet.addAll(legacyMap.values());
        }
        servicesChanged = false;
        return serviceSet;
    }
    
    protected synchronized void putService(Provider$Service s) {
        check("putProviderProperty." + name);
        if (debug != null) {
            debug.println(name + ".putService(): " + s);
        }
        if (s == null) {
            throw new NullPointerException();
        }
        if (serviceMap == null) {
            serviceMap = new LinkedHashMap();
        }
        servicesChanged = true;
        String type = s.getType();
        String algorithm = s.getAlgorithm();
        Provider$ServiceKey key = new Provider$ServiceKey(type, algorithm, true, null);
        implRemoveService((Provider$Service)serviceMap.get(key));
        serviceMap.put(key, s);
        for (Iterator i$ = Provider.Service.access$700(s).iterator(); i$.hasNext(); ) {
            String alias = (String)i$.next();
            {
                serviceMap.put(new Provider$ServiceKey(type, alias, true, null), s);
            }
        }
        putPropertyStrings(s);
    }
    
    private void putPropertyStrings(Provider$Service s) {
        String type = s.getType();
        String algorithm = s.getAlgorithm();
        super.put(type + "." + algorithm, s.getClassName());
        for (Iterator i$ = Provider.Service.access$700(s).iterator(); i$.hasNext(); ) {
            String alias = (String)i$.next();
            {
                super.put(ALIAS_PREFIX + type + "." + alias, algorithm);
            }
        }
        for (Iterator i$ = Provider.Service.access$800(s).entrySet().iterator(); i$.hasNext(); ) {
            Map$Entry entry = (Map$Entry)i$.next();
            {
                String key = type + "." + algorithm + " " + entry.getKey();
                super.put(key, entry.getValue());
            }
        }
    }
    
    private void removePropertyStrings(Provider$Service s) {
        String type = s.getType();
        String algorithm = s.getAlgorithm();
        super.remove(type + "." + algorithm);
        for (Iterator i$ = Provider.Service.access$700(s).iterator(); i$.hasNext(); ) {
            String alias = (String)i$.next();
            {
                super.remove(ALIAS_PREFIX + type + "." + alias);
            }
        }
        for (Iterator i$ = Provider.Service.access$800(s).entrySet().iterator(); i$.hasNext(); ) {
            Map$Entry entry = (Map$Entry)i$.next();
            {
                String key = type + "." + algorithm + " " + entry.getKey();
                super.remove(key);
            }
        }
    }
    
    protected synchronized void removeService(Provider$Service s) {
        check("removeProviderProperty." + name);
        if (debug != null) {
            debug.println(name + ".removeService(): " + s);
        }
        if (s == null) {
            throw new NullPointerException();
        }
        implRemoveService(s);
    }
    
    private void implRemoveService(Provider$Service s) {
        if ((s == null) || (serviceMap == null)) {
            return;
        }
        String type = s.getType();
        String algorithm = s.getAlgorithm();
        Provider$ServiceKey key = new Provider$ServiceKey(type, algorithm, false, null);
        Provider$Service oldService = (Provider$Service)serviceMap.get(key);
        if (s != oldService) {
            return;
        }
        servicesChanged = true;
        serviceMap.remove(key);
        for (Iterator i$ = Provider.Service.access$700(s).iterator(); i$.hasNext(); ) {
            String alias = (String)i$.next();
            {
                serviceMap.remove(new Provider$ServiceKey(type, alias, false, null));
            }
        }
        removePropertyStrings(s);
    }
    {
    }
    {
    }
    private static final Map knownEngines;
    
    private static void addEngine(String name, boolean cons, boolean sp) {
        Provider$EngineDescription ed = new Provider$EngineDescription(name, cons, sp);
        knownEngines.put(name.toLowerCase(Locale.ENGLISH), ed);
        knownEngines.put(name, ed);
    }
    static {
        knownEngines = new HashMap();
        addEngine("AlgorithmParameterGenerator", false, false);
        addEngine("AlgorithmParameters", false, false);
        addEngine("KeyFactory", false, false);
        addEngine("KeyPairGenerator", false, false);
        addEngine("KeyStore", false, false);
        addEngine("MessageDigest", false, false);
        addEngine("SecureRandom", false, false);
        addEngine("Signature", false, true);
        addEngine("CertificateFactory", false, false);
        addEngine("CertPathBuilder", false, false);
        addEngine("CertPathValidator", false, false);
        addEngine("CertStore", true, false);
        addEngine("Cipher", false, true);
        addEngine("ExemptionMechanism", false, false);
        addEngine("Mac", false, true);
        addEngine("KeyAgreement", false, true);
        addEngine("KeyGenerator", false, false);
        addEngine("SecretKeyFactory", false, false);
        addEngine("KeyManagerFactory", false, false);
        addEngine("SSLContext", false, false);
        addEngine("TrustManagerFactory", false, false);
        addEngine("GssApiMechanism", false, false);
        addEngine("SaslClientFactory", false, false);
        addEngine("SaslServerFactory", false, false);
    }
    
    private static String getEngineName(String s) {
        Provider$EngineDescription e = (Provider$EngineDescription)knownEngines.get(s);
        if (e == null) {
            e = (Provider$EngineDescription)knownEngines.get(s.toLowerCase(Locale.ENGLISH));
        }
        return (e == null) ? s : e.name;
    }
    {
    }
}
