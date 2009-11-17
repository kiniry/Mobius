package java.nio.channels.spi;

import java.nio.channels.*;

public abstract class AbstractSelectionKey extends SelectionKey {
    
    protected AbstractSelectionKey() {
        
    }
    private volatile boolean valid = true;
    
    public final boolean isValid() {
        return valid;
    }
    
    void invalidate() {
        valid = false;
    }
    
    public final void cancel() {
        synchronized (this) {
            if (valid) {
                valid = false;
                ((AbstractSelector)(AbstractSelector)selector()).cancel(this);
            }
        }
    }
}
