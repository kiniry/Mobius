package java.lang;

import sun.misc.Signal;
import sun.misc.SignalHandler;

class Terminator {
    
    Terminator() {
        
    }
    private static SignalHandler handler = null;
    
    static void setup() {
        if (handler != null) return;
        SignalHandler sh = new Terminator$1();
        handler = sh;
        try {
            Signal.handle(new Signal("HUP"), sh);
            Signal.handle(new Signal("INT"), sh);
            Signal.handle(new Signal("TERM"), sh);
        } catch (IllegalArgumentException e) {
        }
    }
    
    static void teardown() {
    }
}
