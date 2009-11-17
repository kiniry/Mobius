package java.util;

class TaskQueue {
    /*synthetic*/ static final boolean $assertionsDisabled = !TaskQueue.class.desiredAssertionStatus();
    
    TaskQueue() {
        
    }
    private TimerTask[] queue = new TimerTask[128];
    private int size = 0;
    
    int size() {
        return size;
    }
    
    void add(TimerTask task) {
        if (++size == queue.length) {
            TimerTask[] newQueue = new TimerTask[2 * queue.length];
            System.arraycopy(queue, 0, newQueue, 0, size);
            queue = newQueue;
        }
        queue[size] = task;
        fixUp(size);
    }
    
    TimerTask getMin() {
        return queue[1];
    }
    
    TimerTask get(int i) {
        return queue[i];
    }
    
    void removeMin() {
        queue[1] = queue[size];
        queue[size--] = null;
        fixDown(1);
    }
    
    void quickRemove(int i) {
        if (!$assertionsDisabled && !(i <= size)) throw new AssertionError();
        queue[i] = queue[size];
        queue[size--] = null;
    }
    
    void rescheduleMin(long newTime) {
        queue[1].nextExecutionTime = newTime;
        fixDown(1);
    }
    
    boolean isEmpty() {
        return size == 0;
    }
    
    void clear() {
        for (int i = 1; i <= size; i++) queue[i] = null;
        size = 0;
    }
    
    private void fixUp(int k) {
        while (k > 1) {
            int j = k >> 1;
            if (queue[j].nextExecutionTime <= queue[k].nextExecutionTime) break;
            TimerTask tmp = queue[j];
            queue[j] = queue[k];
            queue[k] = tmp;
            k = j;
        }
    }
    
    private void fixDown(int k) {
        int j;
        while ((j = k << 1) <= size && j > 0) {
            if (j < size && queue[j].nextExecutionTime > queue[j + 1].nextExecutionTime) j++;
            if (queue[k].nextExecutionTime <= queue[j].nextExecutionTime) break;
            TimerTask tmp = queue[j];
            queue[j] = queue[k];
            queue[k] = tmp;
            k = j;
        }
    }
    
    void heapify() {
        for (int i = size / 2; i >= 1; i--) fixDown(i);
    }
}
