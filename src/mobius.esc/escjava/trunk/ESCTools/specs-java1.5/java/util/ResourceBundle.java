package java.util;

import java.io.InputStream;
import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import sun.misc.SoftCache;

public abstract class ResourceBundle {
    
    /*synthetic*/ static ReferenceQueue access$100() {
        return referenceQueue;
    }
    private static final ResourceBundle$ResourceCacheKey cacheKey = new ResourceBundle$ResourceCacheKey(null);
    private static final int INITIAL_CACHE_SIZE = 25;
    private static final float CACHE_LOAD_FACTOR = (float)1.0;
    private static final int MAX_BUNDLES_SEARCHED = 3;
    private static final Hashtable underConstruction = new Hashtable(MAX_BUNDLES_SEARCHED, CACHE_LOAD_FACTOR);
    private static final Object NOT_FOUND = new Object();
    private static SoftCache cacheList = new SoftCache(INITIAL_CACHE_SIZE, CACHE_LOAD_FACTOR);
    private static ReferenceQueue referenceQueue = new ReferenceQueue();
    protected ResourceBundle parent = null;
    private Locale locale = null;
    
    public ResourceBundle() {
        
    }
    
    public final String getString(String key) {
        return (String)(String)getObject(key);
    }
    
    public final String[] getStringArray(String key) {
        return (String[])(String[])getObject(key);
    }
    
    public final Object getObject(String key) {
        Object obj = handleGetObject(key);
        if (obj == null) {
            if (parent != null) {
                obj = parent.getObject(key);
            }
            if (obj == null) throw new MissingResourceException("Can\'t find resource for bundle " + this.getClass().getName() + ", key " + key, this.getClass().getName(), key);
        }
        return obj;
    }
    
    public Locale getLocale() {
        return locale;
    }
    
    private void setLocale(String baseName, String bundleName) {
        if (baseName.length() == bundleName.length()) {
            locale = new Locale("", "");
        } else if (baseName.length() < bundleName.length()) {
            int pos = baseName.length();
            String temp = bundleName.substring(pos + 1);
            pos = temp.indexOf('_');
            if (pos == -1) {
                locale = new Locale(temp, "", "");
                return;
            }
            String language = temp.substring(0, pos);
            temp = temp.substring(pos + 1);
            pos = temp.indexOf('_');
            if (pos == -1) {
                locale = new Locale(language, temp, "");
                return;
            }
            String country = temp.substring(0, pos);
            temp = temp.substring(pos + 1);
            locale = new Locale(language, country, temp);
        } else {
            throw new IllegalArgumentException();
        }
    }
    
    private static ClassLoader getLoader() {
        Class[] stack = getClassContext();
        Class c = stack[2];
        ClassLoader cl = (c == null) ? null : c.getClassLoader();
        if (cl == null) {
            cl = ClassLoader.getSystemClassLoader();
        }
        return cl;
    }
    
    private static native Class[] getClassContext();
    
    protected void setParent(ResourceBundle parent) {
        this.parent = parent;
    }
    {
    }
    {
    }
    
    public static final ResourceBundle getBundle(String baseName) {
        return getBundleImpl(baseName, Locale.getDefault(), getLoader());
    }
    
    public static final ResourceBundle getBundle(String baseName, Locale locale) {
        return getBundleImpl(baseName, locale, getLoader());
    }
    
    public static ResourceBundle getBundle(String baseName, Locale locale, ClassLoader loader) {
        if (loader == null) {
            throw new NullPointerException();
        }
        return getBundleImpl(baseName, locale, loader);
    }
    
    private static ResourceBundle getBundleImpl(String baseName, Locale locale, ClassLoader loader) {
        if (baseName == null) {
            throw new NullPointerException();
        }
        String bundleName = baseName;
        String localeSuffix = locale.toString();
        if (localeSuffix.length() > 0) {
            bundleName += "_" + localeSuffix;
        } else if (locale.getVariant().length() > 0) {
            bundleName += "___" + locale.getVariant();
        }
        Locale defaultLocale = Locale.getDefault();
        Object lookup = findBundleInCache(loader, bundleName, defaultLocale);
        if (lookup == NOT_FOUND) {
            throwMissingResourceException(baseName, locale);
        } else if (lookup != null) {
            return (ResourceBundle)(ResourceBundle)lookup;
        }
        Object parent = NOT_FOUND;
        try {
            Object root = findBundle(loader, baseName, defaultLocale, baseName, null);
            if (root == null) {
                putBundleInCache(loader, baseName, defaultLocale, NOT_FOUND);
                root = NOT_FOUND;
            }
            final Vector names = calculateBundleNames(baseName, locale);
            Vector bundlesFound = new Vector(MAX_BUNDLES_SEARCHED);
            boolean foundInMainBranch = (root != NOT_FOUND && names.size() == 0);
            if (!foundInMainBranch) {
                parent = root;
                for (int i = 0; i < names.size(); i++) {
                    bundleName = (String)(String)names.elementAt(i);
                    lookup = findBundle(loader, bundleName, defaultLocale, baseName, parent);
                    bundlesFound.addElement(lookup);
                    if (lookup != null) {
                        parent = lookup;
                        foundInMainBranch = true;
                    }
                }
            }
            parent = root;
            if (!foundInMainBranch) {
                final Vector fallbackNames = calculateBundleNames(baseName, defaultLocale);
                for (int i = 0; i < fallbackNames.size(); i++) {
                    bundleName = (String)(String)fallbackNames.elementAt(i);
                    if (names.contains(bundleName)) {
                        break;
                    }
                    lookup = findBundle(loader, bundleName, defaultLocale, baseName, parent);
                    if (lookup != null) {
                        parent = lookup;
                    } else {
                        putBundleInCache(loader, bundleName, defaultLocale, parent);
                    }
                }
            }
            parent = propagate(loader, names, bundlesFound, defaultLocale, parent);
        } catch (Exception e) {
            cleanUpConstructionList();
            throwMissingResourceException(baseName, locale);
        } catch (Error e) {
            cleanUpConstructionList();
            throw e;
        }
        if (parent == NOT_FOUND) {
            throwMissingResourceException(baseName, locale);
        }
        return (ResourceBundle)(ResourceBundle)parent;
    }
    
    private static Object propagate(ClassLoader loader, Vector names, Vector bundlesFound, Locale defaultLocale, Object parent) {
        for (int i = 0; i < names.size(); i++) {
            final String bundleName = (String)(String)names.elementAt(i);
            final Object lookup = bundlesFound.elementAt(i);
            if (lookup == null) {
                putBundleInCache(loader, bundleName, defaultLocale, parent);
            } else {
                parent = lookup;
            }
        }
        return parent;
    }
    
    private static void throwMissingResourceException(String baseName, Locale locale) throws MissingResourceException {
        throw new MissingResourceException("Can\'t find bundle for base name " + baseName + ", locale " + locale, baseName + "_" + locale, "");
    }
    
    private static void cleanUpConstructionList() {
        synchronized (cacheList) {
            final Collection entries = underConstruction.values();
            final Thread thisThread = Thread.currentThread();
            while (entries.remove(thisThread)) {
            }
            cacheList.notifyAll();
        }
    }
    
    private static Object findBundle(ClassLoader loader, String bundleName, Locale defaultLocale, String baseName, Object parent) {
        Object result;
        synchronized (cacheList) {
            Reference ref = referenceQueue.poll();
            while (ref != null) {
                cacheList.remove(((ResourceBundle$LoaderReference)(ResourceBundle$LoaderReference)ref).getCacheKey());
                ref = referenceQueue.poll();
            }
            cacheKey.setKeyValues(loader, bundleName, defaultLocale);
            result = cacheList.get(cacheKey);
            if (result != null) {
                cacheKey.clear();
                return result;
            }
            Thread builder = (Thread)(Thread)underConstruction.get(cacheKey);
            boolean beingBuilt = (builder != null && builder != Thread.currentThread());
            if (beingBuilt) {
                while (beingBuilt) {
                    cacheKey.clear();
                    try {
                        cacheList.wait();
                    } catch (InterruptedException e) {
                    }
                    cacheKey.setKeyValues(loader, bundleName, defaultLocale);
                    beingBuilt = underConstruction.containsKey(cacheKey);
                }
                result = cacheList.get(cacheKey);
                if (result != null) {
                    cacheKey.clear();
                    return result;
                }
            }
            final Object key = cacheKey.clone();
            underConstruction.put(key, Thread.currentThread());
            cacheKey.clear();
        }
        result = loadBundle(loader, bundleName, defaultLocale);
        if (result != null) {
            boolean constructing;
            synchronized (cacheList) {
                cacheKey.setKeyValues(loader, bundleName, defaultLocale);
                constructing = underConstruction.get(cacheKey) == Thread.currentThread();
                cacheKey.clear();
            }
            if (constructing) {
                final ResourceBundle bundle = (ResourceBundle)(ResourceBundle)result;
                if (parent != NOT_FOUND && bundle.parent == null) {
                    bundle.setParent((ResourceBundle)(ResourceBundle)parent);
                }
                bundle.setLocale(baseName, bundleName);
                putBundleInCache(loader, bundleName, defaultLocale, result);
            }
        }
        return result;
    }
    
    private static Vector calculateBundleNames(String baseName, Locale locale) {
        final Vector result = new Vector(MAX_BUNDLES_SEARCHED);
        final String language = locale.getLanguage();
        final int languageLength = language.length();
        final String country = locale.getCountry();
        final int countryLength = country.length();
        final String variant = locale.getVariant();
        final int variantLength = variant.length();
        if (languageLength + countryLength + variantLength == 0) {
            return result;
        }
        final StringBuffer temp = new StringBuffer(baseName);
        temp.append('_');
        temp.append(language);
        if (languageLength > 0) {
            result.addElement(temp.toString());
        }
        if (countryLength + variantLength == 0) {
            return result;
        }
        temp.append('_');
        temp.append(country);
        if (countryLength > 0) {
            result.addElement(temp.toString());
        }
        if (variantLength == 0) {
            return result;
        }
        temp.append('_');
        temp.append(variant);
        result.addElement(temp.toString());
        return result;
    }
    
    private static Object findBundleInCache(ClassLoader loader, String bundleName, Locale defaultLocale) {
        synchronized (cacheList) {
            cacheKey.setKeyValues(loader, bundleName, defaultLocale);
            Object result = cacheList.get(cacheKey);
            cacheKey.clear();
            return result;
        }
    }
    
    private static void putBundleInCache(ClassLoader loader, String bundleName, Locale defaultLocale, Object value) {
        synchronized (cacheList) {
            cacheKey.setKeyValues(loader, bundleName, defaultLocale);
            cacheList.put(cacheKey.clone(), value);
            underConstruction.remove(cacheKey);
            cacheKey.clear();
            cacheList.notifyAll();
        }
    }
    
    private static Object loadBundle(final ClassLoader loader, String bundleName, Locale defaultLocale) {
        try {
            Class bundleClass;
            if (loader != null) {
                bundleClass = loader.loadClass(bundleName);
            } else {
                bundleClass = Class.forName(bundleName);
            }
            if (ResourceBundle.class.isAssignableFrom(bundleClass)) {
                Object myBundle = bundleClass.newInstance();
                Object otherBundle = findBundleInCache(loader, bundleName, defaultLocale);
                if (otherBundle != null) {
                    return otherBundle;
                } else {
                    return myBundle;
                }
            }
        } catch (Exception e) {
        } catch (LinkageError e) {
        }
        final String resName = bundleName.replace('.', '/') + ".properties";
        InputStream stream = (InputStream)(InputStream)java.security.AccessController.doPrivileged(new ResourceBundle$1(loader, resName));
        if (stream != null) {
            stream = new java.io.BufferedInputStream(stream);
            try {
                return new PropertyResourceBundle(stream);
            } catch (Exception e) {
            } finally {
                try {
                    stream.close();
                } catch (Exception e) {
                }
            }
        }
        return null;
    }
    
    protected abstract Object handleGetObject(String key);
    
    public abstract Enumeration getKeys();
}
