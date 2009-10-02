package java.security;

import java.io.*;
import java.util.*;
import java.lang.ref.*;
import java.lang.reflect.*;
import java.security.cert.CertStoreParameters;

public class Provider$Service {
    
    /*synthetic*/ static Map access$800(Provider$Service x0) {
        return x0.attributes;
    }
    
    /*synthetic*/ static List access$700(Provider$Service x0) {
        return x0.getAliases();
    }
    
    /*synthetic*/ static String access$602(Provider$Service x0, String x1) {
        return x0.className = x1;
    }
    
    /*synthetic*/ static void access$500(Provider$Service x0, String x1) {
        x0.addAlias(x1);
    }
    
    /*synthetic*/ static String access$402(Provider$Service x0, String x1) {
        return x0.algorithm = x1;
    }
    
    /*synthetic*/ static String access$302(Provider$Service x0, String x1) {
        return x0.type = x1;
    }
    
    /*synthetic*/ Provider$Service(Provider x0, java.security.Provider$1 x1) {
        this(x0);
    }
    
    /*synthetic*/ static boolean access$000(Provider$Service x0) {
        return x0.isValid();
    }
    private String type;
    private String algorithm;
    private String className;
    private final Provider provider;
    private List aliases;
    private Map attributes;
    private volatile Reference classRef;
    private volatile Boolean hasKeyAttributes;
    private String[] supportedFormats;
    private Class[] supportedClasses;
    private static final Class[] CLASS0 = new Class[0];
    
    private Provider$Service(Provider provider) {
        
        this.provider = provider;
        aliases = Collections.emptyList();
        attributes = Collections.emptyMap();
    }
    
    private boolean isValid() {
        return (type != null) && (algorithm != null) && (className != null);
    }
    
    private void addAlias(String alias) {
        if (aliases.isEmpty()) {
            aliases = new ArrayList(2);
        }
        aliases.add(alias);
    }
    
    void addAttribute(String type, String value) {
        if (attributes.isEmpty()) {
            attributes = new HashMap(8);
        }
        attributes.put(new Provider$UString(type), value);
    }
    
    public Provider$Service(Provider provider, String type, String algorithm, String className, List aliases, Map attributes) {
        
        if ((provider == null) || (type == null) || (algorithm == null) || (className == null)) {
            throw new NullPointerException();
        }
        this.provider = provider;
        this.type = Provider.access$900(type);
        this.algorithm = algorithm;
        this.className = className;
        if (aliases == null) {
            this.aliases = Collections.emptyList();
        } else {
            this.aliases = new ArrayList(aliases);
        }
        if (attributes == null) {
            this.attributes = Collections.emptyMap();
        } else {
            this.attributes = new HashMap();
            for (Iterator i$ = attributes.entrySet().iterator(); i$.hasNext(); ) {
                Map$Entry entry = (Map$Entry)i$.next();
                {
                    this.attributes.put(new Provider$UString((String)entry.getKey()), entry.getValue());
                }
            }
        }
    }
    
    public final String getType() {
        return type;
    }
    
    public final String getAlgorithm() {
        return algorithm;
    }
    
    public final Provider getProvider() {
        return provider;
    }
    
    public final String getClassName() {
        return className;
    }
    
    private final List getAliases() {
        return aliases;
    }
    
    public final String getAttribute(String name) {
        if (name == null) {
            throw new NullPointerException();
        }
        return (String)attributes.get(new Provider$UString(name));
    }
    
    public Object newInstance(Object constructorParameter) throws NoSuchAlgorithmException {
        try {
            Provider$EngineDescription cap = (Provider$EngineDescription)Provider.access$1000().get(type);
            if (cap == null) {
                return newInstanceGeneric(constructorParameter);
            }
            if (cap.constructor == false) {
                if (constructorParameter != null) {
                    throw new InvalidParameterException("constructorParameter not used with " + type + " engines");
                }
                Class clazz = getImplClass();
                return clazz.newInstance();
            }
            if (type.equals("CertStore") == false) {
                throw new AssertionError("Unknown engine: " + type);
            }
            if (constructorParameter != null && !(constructorParameter instanceof CertStoreParameters)) {
                throw new InvalidParameterException("constructorParameter must be instanceof CertStoreParameters for CertStores");
            }
            Class clazz = getImplClass();
            Constructor cons = clazz.getConstructor(new Class[]{Class.forName("java.security.cert.CertStoreParameters")});
            return cons.newInstance(new Object[]{constructorParameter});
        } catch (NoSuchAlgorithmException e) {
            throw e;
        } catch (InvocationTargetException e) {
            throw new NoSuchAlgorithmException("Error constructing implementation (algorithm: " + algorithm + ", provider: " + provider.getName() + ", class: " + className + ")", e.getCause());
        } catch (Exception e) {
            throw new NoSuchAlgorithmException("Error constructing implementation (algorithm: " + algorithm + ", provider: " + provider.getName() + ", class: " + className + ")", e);
        }
    }
    
    private Class getImplClass() throws NoSuchAlgorithmException {
        try {
            Reference ref = classRef;
            Class clazz = (ref == null) ? null : (Class)ref.get();
            if (clazz == null) {
                ClassLoader cl = provider.getClass().getClassLoader();
                if (cl == null) {
                    clazz = Class.forName(className);
                } else {
                    clazz = cl.loadClass(className);
                }
                classRef = new WeakReference(clazz);
            }
            return clazz;
        } catch (ClassNotFoundException e) {
            throw new NoSuchAlgorithmException("class configured for " + type + "(provider: " + provider.getName() + ")" + "cannot be found.", e);
        }
    }
    
    private Object newInstanceGeneric(Object constructorParameter) throws Exception {
        Class clazz = getImplClass();
        if (constructorParameter == null) {
            Object o = clazz.newInstance();
            return o;
        }
        Class argClass = constructorParameter.getClass();
        Constructor[] cons = clazz.getConstructors();
        for (int i = 0; i < cons.length; i++) {
            Constructor con = cons[i];
            Class[] paramTypes = con.getParameterTypes();
            if (paramTypes.length != 1) {
                continue;
            }
            if (paramTypes[0].isAssignableFrom(argClass) == false) {
                continue;
            }
            Object o = con.newInstance(new Object[]{constructorParameter});
            return o;
        }
        throw new NoSuchAlgorithmException("No constructor matching " + argClass.getName() + " found in class " + className);
    }
    
    public boolean supportsParameter(Object parameter) {
        Provider$EngineDescription cap = (Provider$EngineDescription)Provider.access$1000().get(type);
        if (cap == null) {
            return true;
        }
        if (cap.supportsParameter == false) {
            throw new InvalidParameterException("supportsParameter() not " + "used with " + type + " engines");
        }
        if ((parameter != null) && (parameter instanceof Key == false)) {
            throw new InvalidParameterException("Parameter must be instanceof Key for engine " + type);
        }
        if (hasKeyAttributes() == false) {
            return true;
        }
        if (parameter == null) {
            return false;
        }
        Key key = (Key)(Key)parameter;
        if (supportsKeyFormat(key)) {
            return true;
        }
        if (supportsKeyClass(key)) {
            return true;
        }
        return false;
    }
    
    private boolean hasKeyAttributes() {
        Boolean b = hasKeyAttributes;
        if (b == null) {
            synchronized (this) {
                String s;
                s = getAttribute("SupportedKeyFormats");
                if (s != null) {
                    supportedFormats = s.split("\\|");
                }
                s = getAttribute("SupportedKeyClasses");
                if (s != null) {
                    String[] classNames = s.split("\\|");
                    List classList = new ArrayList(classNames.length);
                    for (String[] arr$ = classNames, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
                        String className = arr$[i$];
                        {
                            Class clazz = getKeyClass(className);
                            if (clazz != null) {
                                classList.add(clazz);
                            }
                        }
                    }
                    supportedClasses = (Class[])classList.toArray(CLASS0);
                }
                boolean bool = (supportedFormats != null) || (supportedClasses != null);
                b = Boolean.valueOf(bool);
                hasKeyAttributes = b;
            }
        }
        return b.booleanValue();
    }
    
    private Class getKeyClass(String name) {
        try {
            return Class.forName(name);
        } catch (ClassNotFoundException e) {
        }
        try {
            ClassLoader cl = provider.getClass().getClassLoader();
            if (cl != null) {
                return cl.loadClass(name);
            }
        } catch (ClassNotFoundException e) {
        }
        return null;
    }
    
    private boolean supportsKeyFormat(Key key) {
        if (supportedFormats == null) {
            return false;
        }
        String format = key.getFormat();
        if (format == null) {
            return false;
        }
        for (String[] arr$ = supportedFormats, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            String supportedFormat = arr$[i$];
            {
                if (supportedFormat.equals(format)) {
                    return true;
                }
            }
        }
        return false;
    }
    
    private boolean supportsKeyClass(Key key) {
        if (supportedClasses == null) {
            return false;
        }
        Class keyClass = key.getClass();
        for (Class[] arr$ = supportedClasses, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            Class clazz = arr$[i$];
            {
                if (clazz.isAssignableFrom(keyClass)) {
                    return true;
                }
            }
        }
        return false;
    }
    
    public String toString() {
        String aString = aliases.isEmpty() ? "" : "\r\n  aliases: " + aliases.toString();
        String attrs = attributes.isEmpty() ? "" : "\r\n  attributes: " + attributes.toString();
        return provider.getName() + ": " + type + "." + algorithm + " -> " + className + aString + attrs + "\r\n";
    }
}
