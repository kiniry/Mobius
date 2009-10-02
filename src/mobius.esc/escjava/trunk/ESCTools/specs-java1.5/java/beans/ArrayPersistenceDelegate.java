package java.beans;

import java.lang.reflect.Array;

class ArrayPersistenceDelegate extends PersistenceDelegate {
    
    ArrayPersistenceDelegate() {
        
    }
    
    protected boolean mutatesTo(Object oldInstance, Object newInstance) {
        return (newInstance != null && oldInstance.getClass() == newInstance.getClass() && Array.getLength(oldInstance) == Array.getLength(newInstance));
    }
    
    protected Expression instantiate(Object oldInstance, Encoder out) {
        Class oldClass = oldInstance.getClass();
        return new Expression(oldInstance, Array.class, "newInstance", new Object[]{oldClass.getComponentType(), new Integer(Array.getLength(oldInstance))});
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        int n = Array.getLength(oldInstance);
        for (int i = 0; i < n; i++) {
            Object index = new Integer(i);
            Expression oldGetExp = new Expression(oldInstance, "get", new Object[]{index});
            Expression newGetExp = new Expression(newInstance, "get", new Object[]{index});
            try {
                Object oldValue = oldGetExp.getValue();
                Object newValue = newGetExp.getValue();
                out.writeExpression(oldGetExp);
                if (!MetaData.equals(newValue, out.get(oldValue))) {
                    DefaultPersistenceDelegate.invokeStatement(oldInstance, "set", new Object[]{index, oldValue}, out);
                }
            } catch (Exception e) {
                out.getExceptionListener().exceptionThrown(e);
            }
        }
    }
}
