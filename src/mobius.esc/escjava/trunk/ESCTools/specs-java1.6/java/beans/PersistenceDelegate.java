package java.beans;

public abstract class PersistenceDelegate {
    
    public PersistenceDelegate() {
        
    }
    
    public void writeObject(Object oldInstance, Encoder out) {
        Object newInstance = out.get(oldInstance);
        if (!mutatesTo(oldInstance, newInstance)) {
            out.remove(oldInstance);
            out.writeExpression(instantiate(oldInstance, out));
        } else {
            initialize(oldInstance.getClass(), oldInstance, newInstance, out);
        }
    }
    
    protected boolean mutatesTo(Object oldInstance, Object newInstance) {
        return (newInstance != null && oldInstance != null && oldInstance.getClass() == newInstance.getClass());
    }
    
    protected abstract Expression instantiate(Object oldInstance, Encoder out);
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        Class superType = type.getSuperclass();
        PersistenceDelegate info = out.getPersistenceDelegate(superType);
        info.initialize(superType, oldInstance, newInstance, out);
    }
}
