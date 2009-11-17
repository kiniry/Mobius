package javax.accessibility;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Locale;
import java.util.MissingResourceException;
import java.util.ResourceBundle;

public abstract class AccessibleBundle {
    private static Hashtable table = new Hashtable();
    private final String defaultResourceBundleName = "com.sun.accessibility.internal.resources.accessibility";
    
    public AccessibleBundle() {
        
    }
    protected String key = null;
    
    protected String toDisplayString(String resourceBundleName, Locale locale) {
        loadResourceBundle(resourceBundleName, locale);
        Object o = table.get(locale);
        if (o != null && o instanceof Hashtable) {
            Hashtable resourceTable = (Hashtable)(Hashtable)o;
            o = resourceTable.get(key);
            if (o != null && o instanceof String) {
                return (String)(String)o;
            }
        }
        return key;
    }
    
    public String toDisplayString(Locale locale) {
        return toDisplayString(defaultResourceBundleName, locale);
    }
    
    public String toDisplayString() {
        return toDisplayString(Locale.getDefault());
    }
    
    public String toString() {
        return toDisplayString();
    }
    
    private void loadResourceBundle(String resourceBundleName, Locale locale) {
        if (!table.contains(locale)) {
            try {
                Hashtable resourceTable = new Hashtable();
                ResourceBundle bundle = ResourceBundle.getBundle(resourceBundleName, locale);
                Enumeration iter = bundle.getKeys();
                while (iter.hasMoreElements()) {
                    String key = (String)(String)iter.nextElement();
                    resourceTable.put(key, bundle.getObject(key));
                }
                table.put(locale, resourceTable);
            } catch (MissingResourceException e) {
                System.err.println("loadResourceBundle: " + e);
                return;
            }
        }
    }
}
