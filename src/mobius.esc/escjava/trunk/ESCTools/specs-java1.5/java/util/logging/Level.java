package java.util.logging;

import java.util.ResourceBundle;

public class Level implements java.io.Serializable {
    private static java.util.ArrayList known = new java.util.ArrayList();
    private static String defaultBundle = "sun.util.logging.resources.logging";
    private final String name;
    private final int value;
    private final String resourceBundleName;
    public static final Level OFF = new Level("OFF", Integer.MAX_VALUE, defaultBundle);
    public static final Level SEVERE = new Level("SEVERE", 1000, defaultBundle);
    public static final Level WARNING = new Level("WARNING", 900, defaultBundle);
    public static final Level INFO = new Level("INFO", 800, defaultBundle);
    public static final Level CONFIG = new Level("CONFIG", 700, defaultBundle);
    public static final Level FINE = new Level("FINE", 500, defaultBundle);
    public static final Level FINER = new Level("FINER", 400, defaultBundle);
    public static final Level FINEST = new Level("FINEST", 300, defaultBundle);
    public static final Level ALL = new Level("ALL", Integer.MIN_VALUE, defaultBundle);
    
    protected Level(String name, int value) {
        this(name, value, null);
    }
    
    protected Level(String name, int value, String resourceBundleName) {
        
        if (name == null) {
            throw new NullPointerException();
        }
        this.name = name;
        this.value = value;
        this.resourceBundleName = resourceBundleName;
        synchronized (Level.class) {
            known.add(this);
        }
    }
    
    public String getResourceBundleName() {
        return resourceBundleName;
    }
    
    public String getName() {
        return name;
    }
    
    public String getLocalizedName() {
        try {
            ResourceBundle rb = ResourceBundle.getBundle(resourceBundleName);
            return rb.getString(name);
        } catch (Exception ex) {
            return name;
        }
    }
    
    public final String toString() {
        return name;
    }
    
    public final int intValue() {
        return value;
    }
    private static final long serialVersionUID = -8176160795706313070L;
    
    private Object readResolve() {
        synchronized (Level.class) {
            for (int i = 0; i < known.size(); i++) {
                Level other = (Level)(Level)known.get(i);
                if (this.name.equals(other.name) && this.value == other.value && (this.resourceBundleName == other.resourceBundleName || (this.resourceBundleName != null && this.resourceBundleName.equals(other.resourceBundleName)))) {
                    return other;
                }
            }
            known.add(this);
            return this;
        }
    }
    
    public static synchronized Level parse(String name) throws IllegalArgumentException {
        name.length();
        for (int i = 0; i < known.size(); i++) {
            Level l = (Level)(Level)known.get(i);
            if (name.equals(l.name)) {
                return l;
            }
        }
        try {
            int x = Integer.parseInt(name);
            for (int i = 0; i < known.size(); i++) {
                Level l = (Level)(Level)known.get(i);
                if (l.value == x) {
                    return l;
                }
            }
            return new Level(name, x);
        } catch (NumberFormatException ex) {
        }
        for (int i = 0; i < known.size(); i++) {
            Level l = (Level)(Level)known.get(i);
            if (name.equals(l.getLocalizedName())) {
                return l;
            }
        }
        throw new IllegalArgumentException("Bad level \"" + name + "\"");
    }
    
    public boolean equals(Object ox) {
        try {
            Level lx = (Level)(Level)ox;
            return (lx.value == this.value);
        } catch (Exception ex) {
            return false;
        }
    }
    
    public int hashCode() {
        return this.value;
    }
}
