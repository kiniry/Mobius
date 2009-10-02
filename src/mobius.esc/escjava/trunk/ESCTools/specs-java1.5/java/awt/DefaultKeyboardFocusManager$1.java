package java.awt;

import java.util.logging.*;
import sun.awt.AppContext;

class DefaultKeyboardFocusManager$1 implements Conditional {
    /*synthetic*/ final AppContext val$targetAppContext;
    /*synthetic*/ final SentEvent val$se;
    
    DefaultKeyboardFocusManager$1(/*synthetic*/ final SentEvent val$se, /*synthetic*/ final AppContext val$targetAppContext) {
        this.val$se = val$se;
        this.val$targetAppContext = val$targetAppContext;
        
    }
    
    public boolean evaluate() {
        return !val$se.dispatched && !val$targetAppContext.isDisposed();
    }
}
