package java.nio.channels.spi;

import java.io.IOException;
import java.nio.channels.SelectionKey;
import java.nio.channels.Selector;
import java.util.HashSet;
import java.util.Set;
import sun.nio.ch.Interruptible;
import java.util.concurrent.atomic.AtomicBoolean;

public abstract class AbstractSelector extends Selector {
    private AtomicBoolean selectorOpen = new AtomicBoolean(true);
    private final SelectorProvider provider;
    
    protected AbstractSelector(SelectorProvider provider) {
        
        this.provider = provider;
    }
    private final Set cancelledKeys = new HashSet();
    
    void cancel(SelectionKey k) {
        synchronized (cancelledKeys) {
            cancelledKeys.add(k);
        }
    }
    
    public final void close() throws IOException {
        boolean open = selectorOpen.getAndSet(false);
        if (!open) return;
        implCloseSelector();
    }
    
    protected abstract void implCloseSelector() throws IOException;
    
    public final boolean isOpen() {
        return selectorOpen.get();
    }
    
    public final SelectorProvider provider() {
        return provider;
    }
    
    protected final Set cancelledKeys() {
        return cancelledKeys;
    }
    
    protected abstract SelectionKey register(AbstractSelectableChannel ch, int ops, Object att);
    
    protected final void deregister(AbstractSelectionKey key) {
        ((AbstractSelectableChannel)(AbstractSelectableChannel)key.channel()).removeKey(key);
    }
    private Interruptible interruptor = null;
    
    protected final void begin() {
        if (interruptor == null) {
            interruptor = new AbstractSelector$1(this);
        }
        AbstractInterruptibleChannel.blockedOn(interruptor);
        if (Thread.currentThread().isInterrupted()) interruptor.interrupt();
    }
    
    protected final void end() {
        AbstractInterruptibleChannel.blockedOn(null);
    }
}
