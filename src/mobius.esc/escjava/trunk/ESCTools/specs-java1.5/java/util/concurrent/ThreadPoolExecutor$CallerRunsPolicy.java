package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

public class ThreadPoolExecutor$CallerRunsPolicy implements RejectedExecutionHandler {
    
    public ThreadPoolExecutor$CallerRunsPolicy() {
        
    }
    
    public void rejectedExecution(Runnable r, ThreadPoolExecutor e) {
        if (!e.isShutdown()) {
            r.run();
        }
    }
}
