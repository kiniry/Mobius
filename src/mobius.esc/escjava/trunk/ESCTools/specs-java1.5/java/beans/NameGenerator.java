package java.beans;

import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;

class NameGenerator {
    private Map valueToName;
    private Map nameToCount;
    
    public NameGenerator() {
        
        valueToName = new IdentityHashMap();
        nameToCount = new HashMap();
    }
    
    public void clear() {
        valueToName.clear();
        nameToCount.clear();
    }
    
    public static String unqualifiedClassName(Class type) {
        if (type.isArray()) {
            return unqualifiedClassName(type.getComponentType()) + "Array";
        }
        String name = type.getName();
        return name.substring(name.lastIndexOf('.') + 1);
    }
    
    public static String capitalize(String name) {
        if (name == null || name.length() == 0) {
            return name;
        }
        return name.substring(0, 1).toUpperCase(.java.util.Locale.ENGLISH) + name.substring(1);
    }
    
    public String instanceName(Object instance) {
        if (instance == null) {
            return "null";
        }
        if (instance instanceof Class) {
            return unqualifiedClassName((Class)(Class)instance);
        } else {
            String result = (String)(String)valueToName.get(instance);
            if (result != null) {
                return result;
            }
            Class type = instance.getClass();
            String className = unqualifiedClassName(type);
            Object size = nameToCount.get(className);
            int instanceNumber = (size == null) ? 0 : ((Integer)(Integer)size).intValue() + 1;
            nameToCount.put(className, new Integer(instanceNumber));
            result = className + instanceNumber;
            valueToName.put(instance, result);
            return result;
        }
    }
}
