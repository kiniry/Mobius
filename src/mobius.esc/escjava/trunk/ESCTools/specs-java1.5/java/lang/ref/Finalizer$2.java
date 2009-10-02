package java.lang.ref;

class Finalizer$2 implements Runnable {
    
    Finalizer$2() {
        
    }
    
    public void run() {
        for (; ; ) {
            Finalizer f = (Finalizer)(Finalizer)Finalizer.access$000().poll();
            if (f == null) break;
            Finalizer.access$100(f);
        }
    }
}
