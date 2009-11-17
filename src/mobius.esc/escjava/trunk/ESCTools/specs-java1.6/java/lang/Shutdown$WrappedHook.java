package java.lang;

class Shutdown$WrappedHook {
    
    /*synthetic*/ static Thread access$100(Shutdown$WrappedHook x0) {
        return x0.hook;
    }
    private Thread hook;
    
    Shutdown$WrappedHook(Thread t) {
        
        hook = t;
    }
    
    public int hashCode() {
        return System.identityHashCode(hook);
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof Shutdown$WrappedHook)) return false;
        return (((Shutdown$WrappedHook)(Shutdown$WrappedHook)o).hook == hook);
    }
}
