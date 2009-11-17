package java.util;

import java.io.InputStream;
import java.io.IOException;

public class PropertyResourceBundle extends ResourceBundle {
    
    public PropertyResourceBundle(InputStream stream) throws IOException {
        
        Properties properties = new Properties();
        properties.load(stream);
        lookup = new HashMap(properties);
    }
    
    public Object handleGetObject(String key) {
        if (key == null) {
            throw new NullPointerException();
        }
        return lookup.get(key);
    }
    
    public Enumeration getKeys() {
        ResourceBundle parent = this.parent;
        return new ResourceBundleEnumeration(lookup.keySet(), (parent != null) ? parent.getKeys() : null);
    }
    private Map lookup;
}
