package java.nio.channels.spi;

import java.io.IOException;
import java.nio.channels.*;

public abstract class AbstractSelectableChannel extends SelectableChannel {
    private final SelectorProvider provider;
    private SelectionKey[] keys = null;
    private int keyCount = 0;
    private final Object keyLock = new Object();
    private final Object regLock = new Object();
    boolean blocking = true;
    
    protected AbstractSelectableChannel(SelectorProvider provider) {
        
        this.provider = provider;
    }
    
    public final SelectorProvider provider() {
        return provider;
    }
    
    private void addKey(SelectionKey k) {
        synchronized (keyLock) {
            int i = 0;
            if ((keys != null) && (keyCount < keys.length)) {
                for (i = 0; i < keys.length; i++) if (keys[i] == null) break;
            } else if (keys == null) {
                keys = new SelectionKey[3];
            } else {
                int n = keys.length * 2;
                SelectionKey[] ks = new SelectionKey[n];
                for (i = 0; i < keys.length; i++) ks[i] = keys[i];
                keys = ks;
                i = keyCount;
            }
            keys[i] = k;
            keyCount++;
        }
    }
    
    private SelectionKey findKey(Selector sel) {
        synchronized (keyLock) {
            if (keys == null) return null;
            for (int i = 0; i < keys.length; i++) if ((keys[i] != null) && (keys[i].selector() == sel)) return keys[i];
            return null;
        }
    }
    
    void removeKey(SelectionKey k) {
        synchronized (keyLock) {
            for (int i = 0; i < keys.length; i++) if (keys[i] == k) {
                keys[i] = null;
                keyCount--;
            }
            ((AbstractSelectionKey)(AbstractSelectionKey)k).invalidate();
        }
    }
    
    private boolean haveValidKeys() {
        synchronized (keyLock) {
            if (keyCount == 0) return false;
            for (int i = 0; i < keys.length; i++) {
                if ((keys[i] != null) && keys[i].isValid()) return true;
            }
            return false;
        }
    }
    
    public final boolean isRegistered() {
        synchronized (keyLock) {
            return keyCount != 0;
        }
    }
    
    public final SelectionKey keyFor(Selector sel) {
        return findKey(sel);
    }
    
    public final SelectionKey register(Selector sel, int ops, Object att) throws ClosedChannelException {
        if (!isOpen()) throw new ClosedChannelException();
        if ((ops & ~validOps()) != 0) throw new IllegalArgumentException();
        synchronized (regLock) {
            if (blocking) throw new IllegalBlockingModeException();
            SelectionKey k = findKey(sel);
            if (k != null) {
                k.interestOps(ops);
                k.attach(att);
            }
            if (k == null) {
                k = ((AbstractSelector)(AbstractSelector)sel).register(this, ops, att);
                addKey(k);
            }
            return k;
        }
    }
    
    protected final void implCloseChannel() throws IOException {
        implCloseSelectableChannel();
        synchronized (keyLock) {
            int count = (keys == null) ? 0 : keys.length;
            for (int i = 0; i < count; i++) {
                SelectionKey k = keys[i];
                if (k != null) k.cancel();
            }
        }
    }
    
    protected abstract void implCloseSelectableChannel() throws IOException;
    
    public final boolean isBlocking() {
        synchronized (regLock) {
            return blocking;
        }
    }
    
    public final Object blockingLock() {
        return regLock;
    }
    
    public final SelectableChannel configureBlocking(boolean block) throws IOException {
        if (!isOpen()) throw new ClosedChannelException();
        synchronized (regLock) {
            if (blocking == block) return this;
            if (block && haveValidKeys()) throw new IllegalBlockingModeException();
            implConfigureBlocking(block);
            blocking = block;
        }
        return this;
    }
    
    protected abstract void implConfigureBlocking(boolean block) throws IOException;
}
