package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

public class ThreadPoolExecutor$AbortPolicy implements RejectedExecutionHandler {
    
    public ThreadPoolExecutor$AbortPolicy() {
        
    }
    
    public void rejectedExecution(Runnable r, ThreadPoolExecutor e) {
        throw new RejectedExecutionException();
    }
}
