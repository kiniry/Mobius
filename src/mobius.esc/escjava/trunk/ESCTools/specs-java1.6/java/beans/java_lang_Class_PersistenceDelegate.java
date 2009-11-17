package java.beans;

import java.lang.reflect.Field;

class java_lang_Class_PersistenceDelegate extends PersistenceDelegate {
    
    java_lang_Class_PersistenceDelegate() {
        
    }
    
    protected Expression instantiate(Object oldInstance, Encoder out) {
        Class c = (Class)(Class)oldInstance;
        if (c.isPrimitive()) {
            Field field = null;
            try {
                field = ReflectionUtils.typeToClass(c).getDeclaredField("TYPE");
            } catch (NoSuchFieldException ex) {
                System.err.println("Unknown primitive type: " + c);
            }
            return new Expression(oldInstance, field, "get", new Object[]{null});
        } else if (oldInstance == String.class) {
            return new Expression(oldInstance, "", "getClass", new Object[]{});
        } else if (oldInstance == Class.class) {
            return new Expression(oldInstance, String.class, "getClass", new Object[]{});
        } else {
            return new Expression(oldInstance, Class.class, "forName", new Object[]{c.getName()});
        }
    }
}
