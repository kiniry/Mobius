package java.beans;

import java.lang.ref.Reference;
import java.lang.ref.WeakReference;
import java.lang.ref.SoftReference;

public class FeatureDescriptor {
    private Reference classRef;
    
    public FeatureDescriptor() {
        
    }
    
    public String getName() {
        return name;
    }
    
    public void setName(String name) {
        this.name = name;
    }
    
    public String getDisplayName() {
        if (displayName == null) {
            return getName();
        }
        return displayName;
    }
    
    public void setDisplayName(String displayName) {
        this.displayName = displayName;
    }
    
    public boolean isExpert() {
        return expert;
    }
    
    public void setExpert(boolean expert) {
        this.expert = expert;
    }
    
    public boolean isHidden() {
        return hidden;
    }
    
    public void setHidden(boolean hidden) {
        this.hidden = hidden;
    }
    
    public boolean isPreferred() {
        return preferred;
    }
    
    public void setPreferred(boolean preferred) {
        this.preferred = preferred;
    }
    
    public String getShortDescription() {
        if (shortDescription == null) {
            return getDisplayName();
        }
        return shortDescription;
    }
    
    public void setShortDescription(String text) {
        shortDescription = text;
    }
    
    public void setValue(String attributeName, Object value) {
        if (table == null) {
            table = new java.util.Hashtable();
        }
        table.put(attributeName, value);
    }
    
    public Object getValue(String attributeName) {
        if (table == null) {
            return null;
        }
        return table.get(attributeName);
    }
    
    public java.util.Enumeration attributeNames() {
        if (table == null) {
            table = new java.util.Hashtable();
        }
        return table.keys();
    }
    
    FeatureDescriptor(FeatureDescriptor x, FeatureDescriptor y) {
        
        expert = x.expert | y.expert;
        hidden = x.hidden | y.hidden;
        preferred = x.preferred | y.preferred;
        name = y.name;
        shortDescription = x.shortDescription;
        if (y.shortDescription != null) {
            shortDescription = y.shortDescription;
        }
        displayName = x.displayName;
        if (y.displayName != null) {
            displayName = y.displayName;
        }
        classRef = x.classRef;
        if (y.classRef != null) {
            classRef = y.classRef;
        }
        addTable(x.table);
        addTable(y.table);
    }
    
    FeatureDescriptor(FeatureDescriptor old) {
        
        expert = old.expert;
        hidden = old.hidden;
        preferred = old.preferred;
        name = old.name;
        shortDescription = old.shortDescription;
        displayName = old.displayName;
        classRef = old.classRef;
        addTable(old.table);
    }
    
    private void addTable(java.util.Hashtable t) {
        if (t == null) {
            return;
        }
        java.util.Enumeration keys = t.keys();
        while (keys.hasMoreElements()) {
            String key = (String)(String)keys.nextElement();
            Object value = t.get(key);
            setValue(key, value);
        }
    }
    
    void setClass0(Class cls) {
        classRef = createReference(cls);
    }
    
    Class getClass0() {
        return (Class)(Class)getObject(classRef);
    }
    
    static Reference createReference(Object obj, boolean soft) {
        Reference ref = null;
        if (obj != null) {
            if (soft) {
                ref = new SoftReference(obj);
            } else {
                ref = new WeakReference(obj);
            }
        }
        return ref;
    }
    
    static Reference createReference(Object obj) {
        return createReference(obj, false);
    }
    
    static Object getObject(Reference ref) {
        return (ref == null) ? null : (Object)ref.get();
    }
    
    static String capitalize(String s) {
        return NameGenerator.capitalize(s);
    }
    private boolean expert;
    private boolean hidden;
    private boolean preferred;
    private String shortDescription;
    private String name;
    private String displayName;
    private java.util.Hashtable table;
}
