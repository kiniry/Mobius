package java.util;

class Collections$SynchronizedSet extends Collections$SynchronizedCollection implements Set {
    private static final long serialVersionUID = 487447009682186044L;
    
    Collections$SynchronizedSet(Set s) {
        super(s);
    }
    
    Collections$SynchronizedSet(Set s, Object mutex) {
        super(s, mutex);
    }
    
    public boolean equals(Object o) {
        synchronized (mutex) {
            return c.equals(o);
        }
    }
    
    public int hashCode() {
        synchronized (mutex) {
            return c.hashCode();
        }
    }
}
