package javax.swing;

import java.lang.ref.WeakReference;
import java.lang.ref.ReferenceQueue;

class AbstractActionPropertyChangeListener$OwnedWeakReference extends WeakReference {
    private Object owner;
    
    AbstractActionPropertyChangeListener$OwnedWeakReference(Object target, ReferenceQueue queue, Object owner) {
        super(target, queue);
        this.owner = owner;
    }
    
    public Object getOwner() {
        return owner;
    }
}
