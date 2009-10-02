package java.awt;

import java.util.HashMap;
import java.lang.ref.WeakReference;

public abstract class RenderingHints$Key {
    private static HashMap identitymap = new HashMap(17);
    
    private String getIdentity() {
        return getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(getClass())) + ":" + Integer.toHexString(privatekey);
    }
    
    private static synchronized void recordIdentity(RenderingHints$Key k) {
        Object identity = k.getIdentity();
        Object otherref = identitymap.get(identity);
        if (otherref != null) {
            RenderingHints$Key otherkey = (RenderingHints$Key)(RenderingHints$Key)((WeakReference)(WeakReference)otherref).get();
            if (otherkey != null && otherkey.getClass() == k.getClass()) {
                throw new IllegalArgumentException(identity + " already registered");
            }
        }
        identitymap.put(identity, new WeakReference(k));
    }
    private int privatekey;
    
    protected RenderingHints$Key(int privatekey) {
        
        this.privatekey = privatekey;
        recordIdentity(this);
    }
    
    public abstract boolean isCompatibleValue(Object val);
    
    protected final int intKey() {
        return privatekey;
    }
    
    public final int hashCode() {
        return System.identityHashCode(this);
    }
    
    public final boolean equals(Object o) {
        return this == o;
    }
}
