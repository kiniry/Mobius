package java.util;

public abstract class ListResourceBundle extends ResourceBundle {
    
    public ListResourceBundle() {
        
    }
    
    public final Object handleGetObject(String key) {
        if (lookup == null) {
            loadLookup();
        }
        if (key == null) {
            throw new NullPointerException();
        }
        return lookup.get(key);
    }
    
    public Enumeration getKeys() {
        if (lookup == null) {
            loadLookup();
        }
        ResourceBundle parent = this.parent;
        return new ResourceBundleEnumeration(lookup.keySet(), (parent != null) ? parent.getKeys() : null);
    }
    
    protected abstract Object[][] getContents();
    
    private synchronized void loadLookup() {
        if (lookup != null) return;
        Object[][] contents = getContents();
        HashMap temp = new HashMap(contents.length);
        for (int i = 0; i < contents.length; ++i) {
            String key = (String)(String)contents[i][0];
            Object value = contents[i][1];
            if (key == null || value == null) {
                throw new NullPointerException();
            }
            temp.put(key, value);
        }
        lookup = temp;
    }
    private Map lookup = null;
}
