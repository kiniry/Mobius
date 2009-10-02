package javax.swing;

import javax.swing.plaf.ComponentUI;
import javax.swing.border.*;
import javax.swing.event.SwingPropertyChangeSupport;
import java.lang.reflect.*;
import java.util.HashMap;
import java.util.Map;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.ResourceBundle;
import java.util.Locale;
import java.util.Vector;
import java.util.MissingResourceException;
import java.awt.Font;
import java.awt.Color;
import java.awt.Insets;
import java.awt.Dimension;
import java.lang.reflect.Method;
import java.beans.PropertyChangeListener;
import sun.reflect.misc.MethodUtil;

public class UIDefaults extends Hashtable {
    private static final Object PENDING = new String("Pending");
    private SwingPropertyChangeSupport changeSupport;
    private Vector resourceBundles;
    private Locale defaultLocale = Locale.getDefault();
    private Map resourceCache;
    
    public UIDefaults() {
        super(700, 0.75F);
        resourceCache = new HashMap();
    }
    
    public UIDefaults(Object[] keyValueList) {
        super(keyValueList.length / 2);
        for (int i = 0; i < keyValueList.length; i += 2) {
            super.put(keyValueList[i], keyValueList[i + 1]);
        }
    }
    
    public Object get(Object key) {
        Object value = getFromHashtable(key);
        return (value != null) ? value : getFromResourceBundle(key, null);
    }
    
    private Object getFromHashtable(Object key) {
        Object value = super.get(key);
        if ((value != PENDING) && !(value instanceof UIDefaults$ActiveValue) && !(value instanceof UIDefaults$LazyValue)) {
            return value;
        }
        synchronized (this) {
            value = super.get(key);
            if (value == PENDING) {
                do {
                    try {
                        this.wait();
                    } catch (InterruptedException e) {
                    }
                    value = super.get(key);
                }                 while (value == PENDING);
                return value;
            } else if (value instanceof UIDefaults$LazyValue) {
                super.put(key, PENDING);
            } else if (!(value instanceof UIDefaults$ActiveValue)) {
                return value;
            }
        }
        if (value instanceof UIDefaults$LazyValue) {
            try {
                value = ((UIDefaults$LazyValue)(UIDefaults$LazyValue)value).createValue(this);
            } finally {
                synchronized (this) {
                    if (value == null) {
                        super.remove(key);
                    } else {
                        super.put(key, value);
                    }
                    this.notifyAll();
                }
            }
        } else {
            value = ((UIDefaults$ActiveValue)(UIDefaults$ActiveValue)value).createValue(this);
        }
        return value;
    }
    
    public Object get(Object key, Locale l) {
        Object value = getFromHashtable(key);
        return (value != null) ? value : getFromResourceBundle(key, l);
    }
    
    private Object getFromResourceBundle(Object key, Locale l) {
        if (resourceBundles == null || resourceBundles.isEmpty() || !(key instanceof String)) {
            return null;
        }
        if (l == null) {
            if (defaultLocale == null) return null; else l = (Locale)defaultLocale;
        }
        synchronized (this) {
            return getResourceCache(l).get((String)(String)key);
        }
    }
    
    private Map getResourceCache(Locale l) {
        Map values = (Map)(Map)resourceCache.get(l);
        if (values == null) {
            values = new HashMap();
            for (int i = resourceBundles.size() - 1; i >= 0; i--) {
                String bundleName = (String)(String)resourceBundles.get(i);
                try {
                    ResourceBundle b = ResourceBundle.getBundle(bundleName, l);
                    Enumeration keys = b.getKeys();
                    while (keys.hasMoreElements()) {
                        String key = (String)(String)keys.nextElement();
                        if (values.get(key) == null) {
                            Object value = b.getObject(key);
                            values.put(key, value);
                        }
                    }
                } catch (MissingResourceException mre) {
                }
            }
            resourceCache.put(l, values);
        }
        return values;
    }
    
    public Object put(Object key, Object value) {
        Object oldValue = (value == null) ? super.remove(key) : super.put(key, value);
        if (key instanceof String) {
            firePropertyChange((String)(String)key, oldValue, value);
        }
        return oldValue;
    }
    
    public void putDefaults(Object[] keyValueList) {
        for (int i = 0, max = keyValueList.length; i < max; i += 2) {
            Object value = keyValueList[i + 1];
            if (value == null) {
                super.remove(keyValueList[i]);
            } else {
                super.put(keyValueList[i], value);
            }
        }
        firePropertyChange("UIDefaults", null, null);
    }
    
    public Font getFont(Object key) {
        Object value = get(key);
        return (value instanceof Font) ? (Font)(Font)value : null;
    }
    
    public Font getFont(Object key, Locale l) {
        Object value = get(key, l);
        return (value instanceof Font) ? (Font)(Font)value : null;
    }
    
    public Color getColor(Object key) {
        Object value = get(key);
        return (value instanceof Color) ? (Color)(Color)value : null;
    }
    
    public Color getColor(Object key, Locale l) {
        Object value = get(key, l);
        return (value instanceof Color) ? (Color)(Color)value : null;
    }
    
    public Icon getIcon(Object key) {
        Object value = get(key);
        return (value instanceof Icon) ? (Icon)(Icon)value : null;
    }
    
    public Icon getIcon(Object key, Locale l) {
        Object value = get(key, l);
        return (value instanceof Icon) ? (Icon)(Icon)value : null;
    }
    
    public Border getBorder(Object key) {
        Object value = get(key);
        return (value instanceof Border) ? (Border)(Border)value : null;
    }
    
    public Border getBorder(Object key, Locale l) {
        Object value = get(key, l);
        return (value instanceof Border) ? (Border)(Border)value : null;
    }
    
    public String getString(Object key) {
        Object value = get(key);
        return (value instanceof String) ? (String)(String)value : null;
    }
    
    public String getString(Object key, Locale l) {
        Object value = get(key, l);
        return (value instanceof String) ? (String)(String)value : null;
    }
    
    public int getInt(Object key) {
        Object value = get(key);
        return (value instanceof Integer) ? ((Integer)(Integer)value).intValue() : 0;
    }
    
    public int getInt(Object key, Locale l) {
        Object value = get(key, l);
        return (value instanceof Integer) ? ((Integer)(Integer)value).intValue() : 0;
    }
    
    public boolean getBoolean(Object key) {
        Object value = get(key);
        return (value instanceof Boolean) ? ((Boolean)(Boolean)value).booleanValue() : false;
    }
    
    public boolean getBoolean(Object key, Locale l) {
        Object value = get(key, l);
        return (value instanceof Boolean) ? ((Boolean)(Boolean)value).booleanValue() : false;
    }
    
    public Insets getInsets(Object key) {
        Object value = get(key);
        return (value instanceof Insets) ? (Insets)(Insets)value : null;
    }
    
    public Insets getInsets(Object key, Locale l) {
        Object value = get(key, l);
        return (value instanceof Insets) ? (Insets)(Insets)value : null;
    }
    
    public Dimension getDimension(Object key) {
        Object value = get(key);
        return (value instanceof Dimension) ? (Dimension)(Dimension)value : null;
    }
    
    public Dimension getDimension(Object key, Locale l) {
        Object value = get(key, l);
        return (value instanceof Dimension) ? (Dimension)(Dimension)value : null;
    }
    
    public Class getUIClass(String uiClassID, ClassLoader uiClassLoader) {
        try {
            String className = (String)(String)get(uiClassID);
            if (className != null) {
                Class cls = (Class)(Class)get(className);
                if (cls == null) {
                    if (uiClassLoader == null) {
                        cls = SwingUtilities.loadSystemClass(className);
                    } else {
                        cls = uiClassLoader.loadClass(className);
                    }
                    if (cls != null) {
                        put(className, cls);
                    }
                }
                return cls;
            }
        } catch (ClassNotFoundException e) {
            return null;
        } catch (ClassCastException e) {
            return null;
        }
        return null;
    }
    
    public Class getUIClass(String uiClassID) {
        return getUIClass(uiClassID, null);
    }
    
    protected void getUIError(String msg) {
        System.err.println("UIDefaults.getUI() failed: " + msg);
        try {
            throw new Error();
        } catch (Throwable e) {
            e.printStackTrace();
        }
    }
    
    public ComponentUI getUI(JComponent target) {
        Object cl = get("ClassLoader");
        ClassLoader uiClassLoader = (cl != null) ? (ClassLoader)(ClassLoader)cl : target.getClass().getClassLoader();
        Class uiClass = getUIClass(target.getUIClassID(), uiClassLoader);
        Object uiObject = null;
        if (uiClass == null) {
            getUIError("no ComponentUI class for: " + target);
        } else {
            try {
                Method m = (Method)(Method)get(uiClass);
                if (m == null) {
                    Class acClass = JComponent.class;
                    m = uiClass.getMethod("createUI", new Class[]{acClass});
                    put(uiClass, m);
                }
                uiObject = MethodUtil.invoke(m, null, new Object[]{target});
            } catch (NoSuchMethodException e) {
                getUIError("static createUI() method not found in " + uiClass);
            } catch (Exception e) {
                getUIError("createUI() failed for " + target + " " + e);
            }
        }
        return (ComponentUI)(ComponentUI)uiObject;
    }
    
    public synchronized void addPropertyChangeListener(PropertyChangeListener listener) {
        if (changeSupport == null) {
            changeSupport = new SwingPropertyChangeSupport(this);
        }
        changeSupport.addPropertyChangeListener(listener);
    }
    
    public synchronized void removePropertyChangeListener(PropertyChangeListener listener) {
        if (changeSupport != null) {
            changeSupport.removePropertyChangeListener(listener);
        }
    }
    
    public synchronized PropertyChangeListener[] getPropertyChangeListeners() {
        if (changeSupport == null) {
            return new PropertyChangeListener[0];
        }
        return changeSupport.getPropertyChangeListeners();
    }
    
    protected void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
        if (changeSupport != null) {
            changeSupport.firePropertyChange(propertyName, oldValue, newValue);
        }
    }
    
    public synchronized void addResourceBundle(String bundleName) {
        if (bundleName == null) {
            return;
        }
        if (resourceBundles == null) {
            resourceBundles = new Vector(5);
        }
        if (!resourceBundles.contains(bundleName)) {
            resourceBundles.add(bundleName);
            resourceCache.clear();
        }
    }
    
    public synchronized void removeResourceBundle(String bundleName) {
        if (resourceBundles != null) {
            resourceBundles.remove(bundleName);
        }
        resourceCache.clear();
    }
    
    public void setDefaultLocale(Locale l) {
        defaultLocale = l;
    }
    
    public Locale getDefaultLocale() {
        return defaultLocale;
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
