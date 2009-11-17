package javax.xml.transform;

import java.io.File;
import java.util.Properties;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

class FactoryFinder {
    
    FactoryFinder() {
        
    }
    private static boolean debug = false;
    static Properties cacheProps = new Properties();
    static SecuritySupport ss = new SecuritySupport();
    static boolean firstTime = true;
    static {
        try {
            String val = ss.getSystemProperty("jaxp.debug");
            debug = val != null && (!"false".equals(val));
        } catch (SecurityException se) {
            debug = false;
        }
    }
    
    private static void dPrint(String msg) {
        if (debug) {
            System.err.println("JAXP: " + msg);
        }
    }
    
    private static Object newInstance(String className, ClassLoader cl, boolean doFallback) throws FactoryFinder$ConfigurationError {
        try {
            Class providerClass;
            if (cl == null) {
                providerClass = Class.forName(className);
            } else {
                try {
                    providerClass = cl.loadClass(className);
                } catch (ClassNotFoundException x) {
                    if (doFallback) {
                        cl = FactoryFinder.class.getClassLoader();
                        providerClass = Class.forName(className, true, cl);
                    } else {
                        throw x;
                    }
                }
            }
            Object instance = providerClass.newInstance();
            dPrint("created new instance of " + providerClass + " using ClassLoader: " + cl);
            return instance;
        } catch (ClassNotFoundException x) {
            throw new FactoryFinder$ConfigurationError("Provider " + className + " not found", x);
        } catch (Exception x) {
            throw new FactoryFinder$ConfigurationError("Provider " + className + " could not be instantiated: " + x, x);
        }
    }
    
    static Object find(String factoryId, String fallbackClassName) throws FactoryFinder$ConfigurationError {
        ClassLoader classLoader = ss.getContextClassLoader();
        if (classLoader == null) {
            classLoader = FactoryFinder.class.getClassLoader();
        }
        dPrint("find factoryId =" + factoryId);
        try {
            String systemProp = ss.getSystemProperty(factoryId);
            if (systemProp != null) {
                dPrint("found system property, value=" + systemProp);
                return newInstance(systemProp, classLoader, true);
            }
        } catch (SecurityException se) {
        }
        try {
            String javah = ss.getSystemProperty("java.home");
            String configFile = javah + File.separator + "lib" + File.separator + "jaxp.properties";
            String factoryClassName = null;
            if (firstTime) {
                synchronized (cacheProps) {
                    if (firstTime) {
                        File f = new File(configFile);
                        firstTime = false;
                        if (ss.doesFileExist(f)) {
                            dPrint("Read properties file " + f);
                            cacheProps.load(ss.getFileInputStream(f));
                        }
                    }
                }
            }
            factoryClassName = cacheProps.getProperty(factoryId);
            if (factoryClassName != null) {
                dPrint("found in $java.home/jaxp.properties, value=" + factoryClassName);
                return newInstance(factoryClassName, classLoader, true);
            }
        } catch (Exception ex) {
            if (debug) ex.printStackTrace();
        }
        Object provider = findJarServiceProvider(factoryId);
        if (provider != null) {
            return provider;
        }
        if (fallbackClassName == null) {
            throw new FactoryFinder$ConfigurationError("Provider for " + factoryId + " cannot be found", null);
        }
        dPrint("loaded from fallback value: " + fallbackClassName);
        return newInstance(fallbackClassName, classLoader, true);
    }
    
    private static Object findJarServiceProvider(String factoryId) throws FactoryFinder$ConfigurationError {
        String serviceId = "META-INF/services/" + factoryId;
        InputStream is = null;
        ClassLoader cl = ss.getContextClassLoader();
        if (cl != null) {
            is = ss.getResourceAsStream(cl, serviceId);
            if (is == null) {
                cl = FactoryFinder.class.getClassLoader();
                is = ss.getResourceAsStream(cl, serviceId);
            }
        } else {
            cl = FactoryFinder.class.getClassLoader();
            is = ss.getResourceAsStream(cl, serviceId);
        }
        if (is == null) {
            return null;
        }
        dPrint("found jar resource=" + serviceId + " using ClassLoader: " + cl);
        BufferedReader rd;
        try {
            rd = new BufferedReader(new InputStreamReader(is, "UTF-8"));
        } catch (java.io.UnsupportedEncodingException e) {
            rd = new BufferedReader(new InputStreamReader(is));
        }
        String factoryClassName = null;
        try {
            factoryClassName = rd.readLine();
            rd.close();
        } catch (IOException x) {
            return null;
        }
        if (factoryClassName != null && !"".equals(factoryClassName)) {
            dPrint("found in resource, value=" + factoryClassName);
            return newInstance(factoryClassName, cl, false);
        }
        return null;
    }
    {
    }
}
