package java.lang.ref;

class Finalizer$3 implements Runnable {
    
    Finalizer$3() {
        
    }
    
    public void run() {
        for (; ; ) {
            Finalizer f;
            synchronized (Finalizer.access$200()) {
                f = Finalizer.access$300();
                if (f == null) break;
                Finalizer.access$302(Finalizer.access$400(f));
            }
            Finalizer.access$100(f);
        }
    }
}
