package java.lang.ref;

class Finalizer$FinalizerThread extends Thread {
    
    Finalizer$FinalizerThread(ThreadGroup g) {
        super(g, "Finalizer");
    }
    
    public void run() {
        for (; ; ) {
            try {
                Finalizer f = (Finalizer)(Finalizer)Finalizer.access$000().remove();
                Finalizer.access$100(f);
            } catch (InterruptedException x) {
                continue;
            }
        }
    }
}
