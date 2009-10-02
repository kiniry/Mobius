package java.beans;

import java.lang.reflect.Field;

class java_lang_reflect_Field_PersistenceDelegate extends PersistenceDelegate {
    
    java_lang_reflect_Field_PersistenceDelegate() {
        
    }
    
    protected Expression instantiate(Object oldInstance, Encoder out) {
        Field f = (Field)(Field)oldInstance;
        return new Expression(oldInstance, f.getDeclaringClass(), "getField", new Object[]{f.getName()});
    }
}
