package java.beans;

public class PropertyEditorManager {
    
    public PropertyEditorManager() {
        
    }
    
    public static void registerEditor(Class targetType, Class editorClass) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPropertiesAccess();
        }
        initialize();
        if (editorClass == null) {
            registry.remove(targetType);
        } else {
            registry.put(targetType, editorClass);
        }
    }
    
    public static synchronized PropertyEditor findEditor(Class targetType) {
        initialize();
        Class editorClass = (Class)(Class)registry.get(targetType);
        if (editorClass != null) {
            try {
                Object o = editorClass.newInstance();
                return (PropertyEditor)(PropertyEditor)o;
            } catch (Exception ex) {
                System.err.println("Couldn\'t instantiate type editor \"" + editorClass.getName() + "\" : " + ex);
            }
        }
        String editorName = targetType.getName() + "Editor";
        try {
            return (PropertyEditor)(PropertyEditor)Introspector.instantiate(targetType, editorName);
        } catch (Exception ex) {
        }
        editorName = targetType.getName();
        while (editorName.indexOf('.') > 0) {
            editorName = editorName.substring(editorName.indexOf('.') + 1);
        }
        for (int i = 0; i < searchPath.length; i++) {
            String name = searchPath[i] + "." + editorName + "Editor";
            try {
                return (PropertyEditor)(PropertyEditor)Introspector.instantiate(targetType, name);
            } catch (Exception ex) {
            }
        }
        return null;
    }
    
    public static synchronized String[] getEditorSearchPath() {
        String[] result = new String[searchPath.length];
        for (int i = 0; i < searchPath.length; i++) {
            result[i] = searchPath[i];
        }
        return result;
    }
    
    public static synchronized void setEditorSearchPath(String[] path) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPropertiesAccess();
        }
        initialize();
        if (path == null) {
            path = new String[0];
        }
        searchPath = path;
    }
    
    private static synchronized void load(Class targetType, String name) {
        String editorName = name;
        for (int i = 0; i < searchPath.length; i++) {
            try {
                editorName = searchPath[i] + "." + name;
                Class cls = Class.forName(editorName);
                registry.put(targetType, cls);
                return;
            } catch (Exception ex) {
            }
        }
        System.err.println("load of " + editorName + " failed");
    }
    
    private static synchronized void initialize() {
        if (registry != null) {
            return;
        }
        registry = new java.util.Hashtable();
        load(Byte.TYPE, "ByteEditor");
        load(Short.TYPE, "ShortEditor");
        load(Integer.TYPE, "IntEditor");
        load(Long.TYPE, "LongEditor");
        load(Boolean.TYPE, "BoolEditor");
        load(Float.TYPE, "FloatEditor");
        load(Double.TYPE, "DoubleEditor");
    }
    private static String[] searchPath = {"sun.beans.editors"};
    private static java.util.Hashtable registry;
}
