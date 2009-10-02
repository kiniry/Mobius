package java.security;

import java.lang.reflect.*;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.io.*;
import java.net.URL;
import sun.security.util.Debug;
import sun.security.util.PropertyExpander;
import sun.security.jca.*;

public final class Security {
    
    /*synthetic*/ static void access$000() {
        initialize();
    }
    private static final Debug sdebug = Debug.getInstance("properties");
    private static Properties props;
    {
    }
    static {
        AccessController.doPrivileged(new Security$1());
    }
    
    private static void initialize() {
        props = new Properties();
        boolean loadedProps = false;
        boolean overrideAll = false;
        File propFile = securityPropFile("java.security");
        if (propFile.exists()) {
            try {
                FileInputStream fis = new FileInputStream(propFile);
                InputStream is = new BufferedInputStream(fis);
                props.load(is);
                is.close();
                loadedProps = true;
                if (sdebug != null) {
                    sdebug.println("reading security properties file: " + propFile);
                }
            } catch (IOException e) {
                if (sdebug != null) {
                    sdebug.println("unable to load security properties from " + propFile);
                    e.printStackTrace();
                }
            }
        }
        if ("true".equalsIgnoreCase(props.getProperty("security.overridePropertiesFile"))) {
            String extraPropFile = System.getProperty("java.security.properties");
            if (extraPropFile != null && extraPropFile.startsWith("=")) {
                overrideAll = true;
                extraPropFile = extraPropFile.substring(1);
            }
            if (overrideAll) {
                props = new Properties();
                if (sdebug != null) {
                    sdebug.println("overriding other security properties files!");
                }
            }
            if (extraPropFile != null) {
                try {
                    URL propURL;
                    extraPropFile = PropertyExpander.expand(extraPropFile);
                    propFile = new File(extraPropFile);
                    if (propFile.exists()) {
                        propURL = new URL("file:" + propFile.getCanonicalPath());
                    } else {
                        propURL = new URL(extraPropFile);
                    }
                    BufferedInputStream bis = new BufferedInputStream(propURL.openStream());
                    props.load(bis);
                    bis.close();
                    loadedProps = true;
                    if (sdebug != null) {
                        sdebug.println("reading security properties file: " + propURL);
                        if (overrideAll) {
                            sdebug.println("overriding other security properties files!");
                        }
                    }
                } catch (Exception e) {
                    if (sdebug != null) {
                        sdebug.println("unable to load security properties from " + extraPropFile);
                        e.printStackTrace();
                    }
                }
            }
        }
        if (!loadedProps) {
            initializeStatic();
            if (sdebug != null) {
                sdebug.println("unable to load security properties -- using defaults");
            }
        }
    }
    
    private static void initializeStatic() {
        props.put("security.provider.1", "sun.security.provider.Sun");
        props.put("security.provider.2", "sun.security.rsa.SunRsaSign");
        props.put("security.provider.3", "com.sun.net.ssl.internal.ssl.Provider");
        props.put("security.provider.4", "com.sun.crypto.provider.SunJCE");
        props.put("security.provider.5", "sun.security.jgss.SunProvider");
        props.put("security.provider.6", "com.sun.security.sasl.Provider");
    }
    
    private Security() {
        
    }
    
    private static File securityPropFile(String filename) {
        String sep = File.separator;
        return new File(System.getProperty("java.home") + sep + "lib" + sep + "security" + sep + filename);
    }
    
    private static Security$ProviderProperty getProviderProperty(String key) {
        Security$ProviderProperty entry = null;
        List providers = Providers.getProviderList().providers();
        for (int i = 0; i < providers.size(); i++) {
            String matchKey = null;
            Provider prov = (Provider)(Provider)providers.get(i);
            String prop = prov.getProperty(key);
            if (prop == null) {
                for (Enumeration e = prov.keys(); e.hasMoreElements() && prop == null; ) {
                    matchKey = (String)(String)e.nextElement();
                    if (key.equalsIgnoreCase(matchKey)) {
                        prop = prov.getProperty(matchKey);
                        break;
                    }
                }
            }
            if (prop != null) {
                Security$ProviderProperty newEntry = new Security$ProviderProperty(null);
                newEntry.className = prop;
                newEntry.provider = prov;
                return newEntry;
            }
        }
        return entry;
    }
    
    private static String getProviderProperty(String key, Provider provider) {
        String prop = provider.getProperty(key);
        if (prop == null) {
            for (Enumeration e = provider.keys(); e.hasMoreElements() && prop == null; ) {
                String matchKey = (String)(String)e.nextElement();
                if (key.equalsIgnoreCase(matchKey)) {
                    prop = provider.getProperty(matchKey);
                    break;
                }
            }
        }
        return prop;
    }
    
    
    public static String getAlgorithmProperty(String algName, String propName) {
        Security$ProviderProperty entry = getProviderProperty("Alg." + propName + "." + algName);
        if (entry != null) {
            return entry.className;
        } else {
            return null;
        }
    }
    
    public static synchronized int insertProviderAt(Provider provider, int position) {
        String providerName = provider.getName();
        check("insertProvider." + providerName);
        ProviderList list = Providers.getFullProviderList();
        ProviderList newList = ProviderList.insertAt(list, provider, position - 1);
        if (list == newList) {
            return -1;
        }
        Providers.setProviderList(newList);
        return newList.getIndex(providerName) + 1;
    }
    
    public static int addProvider(Provider provider) {
        return insertProviderAt(provider, 0);
    }
    
    public static synchronized void removeProvider(String name) {
        check("removeProvider." + name);
        ProviderList list = Providers.getFullProviderList();
        ProviderList newList = ProviderList.remove(list, name);
        Providers.setProviderList(newList);
    }
    
    public static Provider[] getProviders() {
        return Providers.getFullProviderList().toArray();
    }
    
    public static Provider getProvider(String name) {
        return Providers.getProviderList().getProvider(name);
    }
    
    public static Provider[] getProviders(String filter) {
        String key = null;
        String value = null;
        int index = filter.indexOf(':');
        if (index == -1) {
            key = filter;
            value = "";
        } else {
            key = filter.substring(0, index);
            value = filter.substring(index + 1);
        }
        Hashtable hashtableFilter = new Hashtable(1);
        hashtableFilter.put(key, value);
        return (getProviders(hashtableFilter));
    }
    
    public static Provider[] getProviders(Map filter) {
        Provider[] allProviders = Security.getProviders();
        Set keySet = filter.keySet();
        LinkedHashSet candidates = new LinkedHashSet(5);
        if ((keySet == null) || (allProviders == null)) {
            return allProviders;
        }
        boolean firstSearch = true;
        for (Iterator ite = keySet.iterator(); ite.hasNext(); ) {
            String key = (String)(String)ite.next();
            String value = (String)(String)filter.get(key);
            LinkedHashSet newCandidates = getAllQualifyingCandidates(key, value, allProviders);
            if (firstSearch) {
                candidates = newCandidates;
                firstSearch = false;
            }
            if ((newCandidates != null) && !newCandidates.isEmpty()) {
                for (Iterator cansIte = candidates.iterator(); cansIte.hasNext(); ) {
                    Provider prov = (Provider)(Provider)cansIte.next();
                    if (!newCandidates.contains(prov)) {
                        cansIte.remove();
                    }
                }
            } else {
                candidates = null;
                break;
            }
        }
        if ((candidates == null) || (candidates.isEmpty())) return null;
        Object[] candidatesArray = candidates.toArray();
        Provider[] result = new Provider[candidatesArray.length];
        for (int i = 0; i < result.length; i++) {
            result[i] = (Provider)(Provider)candidatesArray[i];
        }
        return result;
    }
    private static final Map spiMap = new ConcurrentHashMap();
    
    private static Class getSpiClass(String type) {
        Class clazz = (Class)spiMap.get(type);
        if (clazz != null) {
            return clazz;
        }
        try {
            clazz = Class.forName("java.security." + type + "Spi");
            spiMap.put(type, clazz);
            return clazz;
        } catch (ClassNotFoundException e) {
            throw (Error)(Error)new AssertionError("Spi class not found").initCause(e);
        }
    }
    
    static Object[] getImpl(String algorithm, String type, String provider) throws NoSuchAlgorithmException, NoSuchProviderException {
        if (provider == null) {
            return GetInstance.getInstance(type, getSpiClass(type), algorithm).toArray();
        } else {
            return GetInstance.getInstance(type, getSpiClass(type), algorithm, provider).toArray();
        }
    }
    
    static Object[] getImpl(String algorithm, String type, String provider, Object params) throws NoSuchAlgorithmException, NoSuchProviderException, InvalidAlgorithmParameterException {
        if (provider == null) {
            return GetInstance.getInstance(type, getSpiClass(type), algorithm, params).toArray();
        } else {
            return GetInstance.getInstance(type, getSpiClass(type), algorithm, params, provider).toArray();
        }
    }
    
    static Object[] getImpl(String algorithm, String type, Provider provider) throws NoSuchAlgorithmException {
        return GetInstance.getInstance(type, getSpiClass(type), algorithm, provider).toArray();
    }
    
    static Object[] getImpl(String algorithm, String type, Provider provider, Object params) throws NoSuchAlgorithmException, InvalidAlgorithmParameterException {
        return GetInstance.getInstance(type, getSpiClass(type), algorithm, params, provider).toArray();
    }
    
    public static String getProperty(String key) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(new SecurityPermission("getProperty." + key));
        }
        String name = props.getProperty(key);
        if (name != null) name = name.trim();
        return name;
    }
    
    public static void setProperty(String key, String datum) {
        check("setProperty." + key);
        props.put(key, datum);
        invalidateSMCache(key);
    }
    
    private static void invalidateSMCache(String key) {
        final boolean pa = key.equals("package.access");
        final boolean pd = key.equals("package.definition");
        if (pa || pd) {
            AccessController.doPrivileged(new Security$2(pa));
        }
    }
    
    private static void check(String directive) {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkSecurityAccess(directive);
        }
    }
    
    private static LinkedHashSet getAllQualifyingCandidates(String filterKey, String filterValue, Provider[] allProviders) {
        String[] filterComponents = getFilterComponents(filterKey, filterValue);
        String serviceName = filterComponents[0];
        String algName = filterComponents[1];
        String attrName = filterComponents[2];
        return getProvidersNotUsingCache(serviceName, algName, attrName, filterValue, allProviders);
    }
    
    private static LinkedHashSet getProvidersNotUsingCache(String serviceName, String algName, String attrName, String filterValue, Provider[] allProviders) {
        LinkedHashSet candidates = new LinkedHashSet(5);
        for (int i = 0; i < allProviders.length; i++) {
            if (isCriterionSatisfied(allProviders[i], serviceName, algName, attrName, filterValue)) {
                candidates.add(allProviders[i]);
            }
        }
        return candidates;
    }
    
    private static boolean isCriterionSatisfied(Provider prov, String serviceName, String algName, String attrName, String filterValue) {
        String key = serviceName + '.' + algName;
        if (attrName != null) {
            key += ' ' + attrName;
        }
        String propValue = getProviderProperty(key, prov);
        if (propValue == null) {
            String standardName = getProviderProperty("Alg.Alias." + serviceName + "." + algName, prov);
            if (standardName != null) {
                key = serviceName + "." + standardName;
                if (attrName != null) {
                    key += ' ' + attrName;
                }
                propValue = getProviderProperty(key, prov);
            }
            if (propValue == null) {
                return false;
            }
        }
        if (attrName == null) {
            return true;
        }
        if (isStandardAttr(attrName)) {
            return isConstraintSatisfied(attrName, filterValue, propValue);
        } else {
            return filterValue.equalsIgnoreCase(propValue);
        }
    }
    
    private static boolean isStandardAttr(String attribute) {
        if (attribute.equalsIgnoreCase("KeySize")) return true;
        if (attribute.equalsIgnoreCase("ImplementedIn")) return true;
        return false;
    }
    
    private static boolean isConstraintSatisfied(String attribute, String value, String prop) {
        if (attribute.equalsIgnoreCase("KeySize")) {
            int requestedSize = Integer.parseInt(value);
            int maxSize = Integer.parseInt(prop);
            if (requestedSize <= maxSize) {
                return true;
            } else {
                return false;
            }
        }
        if (attribute.equalsIgnoreCase("ImplementedIn")) {
            return value.equalsIgnoreCase(prop);
        }
        return false;
    }
    
    static String[] getFilterComponents(String filterKey, String filterValue) {
        int algIndex = filterKey.indexOf('.');
        if (algIndex < 0) {
            throw new InvalidParameterException("Invalid filter");
        }
        String serviceName = filterKey.substring(0, algIndex);
        String algName = null;
        String attrName = null;
        if (filterValue.length() == 0) {
            algName = filterKey.substring(algIndex + 1).trim();
            if (algName.length() == 0) {
                throw new InvalidParameterException("Invalid filter");
            }
        } else {
            int attrIndex = filterKey.indexOf(' ');
            if (attrIndex == -1) {
                throw new InvalidParameterException("Invalid filter");
            } else {
                attrName = filterKey.substring(attrIndex + 1).trim();
                if (attrName.length() == 0) {
                    throw new InvalidParameterException("Invalid filter");
                }
            }
            if ((attrIndex < algIndex) || (algIndex == attrIndex - 1)) {
                throw new InvalidParameterException("Invalid filter");
            } else {
                algName = filterKey.substring(algIndex + 1, attrIndex);
            }
        }
        String[] result = new String[3];
        result[0] = serviceName;
        result[1] = algName;
        result[2] = attrName;
        return result;
    }
    
    public static Set getAlgorithms(String serviceName) {
        if ((serviceName == null) || (serviceName.length() == 0) || (serviceName.endsWith("."))) {
            return Collections.EMPTY_SET;
        }
        HashSet result = new HashSet();
        Provider[] providers = Security.getProviders();
        for (int i = 0; i < providers.length; i++) {
            for (Enumeration e = providers[i].keys(); e.hasMoreElements(); ) {
                String currentKey = ((String)(String)e.nextElement()).toUpperCase();
                if (currentKey.startsWith(serviceName.toUpperCase())) {
                    if (currentKey.indexOf(" ") < 0) {
                        result.add(currentKey.substring(serviceName.length() + 1));
                    }
                }
            }
        }
        return Collections.unmodifiableSet(result);
    }
}
