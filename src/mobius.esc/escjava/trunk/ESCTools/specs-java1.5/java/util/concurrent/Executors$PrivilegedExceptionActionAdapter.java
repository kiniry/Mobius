package java.util.concurrent;

import java.util.*;
import java.security.PrivilegedExceptionAction;

final class Executors$PrivilegedExceptionActionAdapter implements Callable {
    
    Executors$PrivilegedExceptionActionAdapter(PrivilegedExceptionAction action) {
        
        this.action = action;
    }
    
    public Object call() throws Exception {
        return action.run();
    }
    private final PrivilegedExceptionAction action;
}
