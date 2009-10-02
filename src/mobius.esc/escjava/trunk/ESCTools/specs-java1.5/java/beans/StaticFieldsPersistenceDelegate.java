package java.beans;

import java.lang.reflect.Field;

class StaticFieldsPersistenceDelegate extends PersistenceDelegate {
    
    StaticFieldsPersistenceDelegate() {
        
    }
    
    protected void installFields(Encoder out, Class cls) {
        Field[] fields = cls.getFields();
        for (int i = 0; i < fields.length; i++) {
            Field field = fields[i];
            if (Object.class.isAssignableFrom(field.getType())) {
                out.writeExpression(new Expression(field, "get", new Object[]{null}));
            }
        }
    }
    
    protected Expression instantiate(Object oldInstance, Encoder out) {
        throw new RuntimeException("Unrecognized instance: " + oldInstance);
    }
    
    public void writeObject(Object oldInstance, Encoder out) {
        if (out.getAttribute(this) == null) {
            out.setAttribute(this, Boolean.TRUE);
            installFields(out, oldInstance.getClass());
        }
        super.writeObject(oldInstance, out);
    }
}
