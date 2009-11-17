package java.beans;

import java.lang.reflect.Method;

class java_lang_reflect_Method_PersistenceDelegate extends PersistenceDelegate {
    
    java_lang_reflect_Method_PersistenceDelegate() {
        
    }
    
    protected Expression instantiate(Object oldInstance, Encoder out) {
        Method m = (Method)(Method)oldInstance;
        return new Expression(oldInstance, m.getDeclaringClass(), "getMethod", new Object[]{m.getName(), m.getParameterTypes()});
    }
}
