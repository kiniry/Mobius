package java.nio.channels.spi;

import java.io.IOException;
import java.nio.channels.*;
import sun.nio.ch.Interruptible;

public abstract class AbstractInterruptibleChannel implements Channel, InterruptibleChannel {
    
    /*synthetic*/ static boolean access$202(AbstractInterruptibleChannel x0, boolean x1) {
        return x0.interrupted = x1;
    }
    
    /*synthetic*/ static boolean access$102(AbstractInterruptibleChannel x0, boolean x1) {
        return x0.open = x1;
    }
    
    /*synthetic*/ static boolean access$100(AbstractInterruptibleChannel x0) {
        return x0.open;
    }
    
    /*synthetic*/ static Object access$000(AbstractInterruptibleChannel x0) {
        return x0.closeLock;
    }
    private Object closeLock = new Object();
    private volatile boolean open = true;
    
    protected AbstractInterruptibleChannel() {
        
    }
    
    public final void close() throws IOException {
        synchronized (closeLock) {
            if (!open) return;
            open = false;
            implCloseChannel();
        }
    }
    
    protected abstract void implCloseChannel() throws IOException;
    
    public final boolean isOpen() {
        return open;
    }
    private Interruptible interruptor;
    private volatile boolean interrupted = false;
    
    protected final void begin() {
        if (interruptor == null) {
            interruptor = new AbstractInterruptibleChannel$1(this);
        }
        blockedOn(interruptor);
        if (Thread.currentThread().isInterrupted()) interruptor.interrupt();
    }
    
    protected final void end(boolean completed) throws AsynchronousCloseException {
        blockedOn(null);
        if (completed) {
            interrupted = false;
            return;
        }
        if (interrupted) throw new ClosedByInterruptException();
        if (!open) throw new AsynchronousCloseException();
    }
    
    static void blockedOn(Interruptible intr) {
        sun.misc.SharedSecrets.getJavaLangAccess().blockedOn(Thread.currentThread(), intr);
    }
}
