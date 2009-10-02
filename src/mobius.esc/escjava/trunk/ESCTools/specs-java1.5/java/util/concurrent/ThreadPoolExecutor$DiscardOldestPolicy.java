package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

public class ThreadPoolExecutor$DiscardOldestPolicy implements RejectedExecutionHandler {
    
    public ThreadPoolExecutor$DiscardOldestPolicy() {
        
    }
    
    public void rejectedExecution(Runnable r, ThreadPoolExecutor e) {
        if (!e.isShutdown()) {
            e.getQueue().poll();
            e.execute(r);
        }
    }
}
