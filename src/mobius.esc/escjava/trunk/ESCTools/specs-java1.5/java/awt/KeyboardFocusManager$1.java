package java.awt;

import java.beans.*;
import java.util.logging.*;
import java.lang.reflect.*;

class KeyboardFocusManager$1 implements Runnable {
    
    KeyboardFocusManager$1() {
        
    }
    
    public void run() {
        KeyboardFocusManager.processCurrentLightweightRequests();
    }
}
