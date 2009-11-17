package java.lang;

import sun.misc.Signal;
import sun.misc.SignalHandler;

class Terminator$1 implements SignalHandler {
    
    Terminator$1() {
        
    }
    
    public void handle(Signal sig) {
        Shutdown.exit(sig.getNumber() + 128);
    }
}
