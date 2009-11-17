package java.util.concurrent;

import java.util.*;
import java.security.PrivilegedAction;

final class Executors$PrivilegedActionAdapter implements Callable {
    
    Executors$PrivilegedActionAdapter(PrivilegedAction action) {
        
        this.action = action;
    }
    
    public Object call() {
        return action.run();
    }
    private final PrivilegedAction action;
}
