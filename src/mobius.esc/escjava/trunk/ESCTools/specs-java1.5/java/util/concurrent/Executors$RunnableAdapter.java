package java.util.concurrent;

import java.util.*;

final class Executors$RunnableAdapter implements Callable {
    final Runnable task;
    final Object result;
    
    Executors$RunnableAdapter(Runnable task, Object result) {
        
        this.task = task;
        this.result = result;
    }
    
    public Object call() {
        task.run();
        return result;
    }
}
