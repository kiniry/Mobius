package java.beans;

class NullPersistenceDelegate extends PersistenceDelegate {
    
    NullPersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
    }
    
    protected Expression instantiate(Object oldInstance, Encoder out) {
        return null;
    }
    
    public void writeObject(Object oldInstance, Encoder out) {
    }
}
