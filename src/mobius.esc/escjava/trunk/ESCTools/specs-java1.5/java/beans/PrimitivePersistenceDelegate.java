package java.beans;

class PrimitivePersistenceDelegate extends PersistenceDelegate {
    
    PrimitivePersistenceDelegate() {
        
    }
    
    protected boolean mutatesTo(Object oldInstance, Object newInstance) {
        return oldInstance.equals(newInstance);
    }
    
    protected Expression instantiate(Object oldInstance, Encoder out) {
        return new Expression(oldInstance, oldInstance.getClass(), "new", new Object[]{oldInstance.toString()});
    }
}
