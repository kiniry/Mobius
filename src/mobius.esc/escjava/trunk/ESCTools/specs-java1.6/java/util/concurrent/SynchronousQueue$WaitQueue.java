package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

abstract class SynchronousQueue$WaitQueue implements java.io.Serializable {
    
    SynchronousQueue$WaitQueue() {
        
    }
    
    abstract SynchronousQueue$Node enq(Object x);
    
    abstract SynchronousQueue$Node deq();
}
