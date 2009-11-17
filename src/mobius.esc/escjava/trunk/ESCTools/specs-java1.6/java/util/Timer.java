package java.util;

import java.util.Date;

public class Timer {
    
    /*synthetic*/ static TimerThread access$100(Timer x0) {
        return x0.thread;
    }
    
    /*synthetic*/ static TaskQueue access$000(Timer x0) {
        return x0.queue;
    }
    private TaskQueue queue = new TaskQueue();
    private TimerThread thread = new TimerThread(queue);
    private Object threadReaper = new Timer$1(this);
    private static int nextSerialNumber = 0;
    
    private static synchronized int serialNumber() {
        return nextSerialNumber++;
    }
    
    public Timer() {
        this("Timer-" + serialNumber());
    }
    
    public Timer(boolean isDaemon) {
        this("Timer-" + serialNumber(), isDaemon);
    }
    
    public Timer(String name) {
        
        thread.setName(name);
        thread.start();
    }
    
    public Timer(String name, boolean isDaemon) {
        
        thread.setName(name);
        thread.setDaemon(isDaemon);
        thread.start();
    }
    
    public void schedule(TimerTask task, long delay) {
        if (delay < 0) throw new IllegalArgumentException("Negative delay.");
        sched(task, System.currentTimeMillis() + delay, 0);
    }
    
    public void schedule(TimerTask task, Date time) {
        sched(task, time.getTime(), 0);
    }
    
    public void schedule(TimerTask task, long delay, long period) {
        if (delay < 0) throw new IllegalArgumentException("Negative delay.");
        if (period <= 0) throw new IllegalArgumentException("Non-positive period.");
        sched(task, System.currentTimeMillis() + delay, -period);
    }
    
    public void schedule(TimerTask task, Date firstTime, long period) {
        if (period <= 0) throw new IllegalArgumentException("Non-positive period.");
        sched(task, firstTime.getTime(), -period);
    }
    
    public void scheduleAtFixedRate(TimerTask task, long delay, long period) {
        if (delay < 0) throw new IllegalArgumentException("Negative delay.");
        if (period <= 0) throw new IllegalArgumentException("Non-positive period.");
        sched(task, System.currentTimeMillis() + delay, period);
    }
    
    public void scheduleAtFixedRate(TimerTask task, Date firstTime, long period) {
        if (period <= 0) throw new IllegalArgumentException("Non-positive period.");
        sched(task, firstTime.getTime(), period);
    }
    
    private void sched(TimerTask task, long time, long period) {
        if (time < 0) throw new IllegalArgumentException("Illegal execution time.");
        synchronized (queue) {
            if (!thread.newTasksMayBeScheduled) throw new IllegalStateException("Timer already cancelled.");
            synchronized (task.lock) {
                if (task.state != TimerTask.VIRGIN) throw new IllegalStateException("Task already scheduled or cancelled");
                task.nextExecutionTime = time;
                task.period = period;
                task.state = TimerTask.SCHEDULED;
            }
            queue.add(task);
            if (queue.getMin() == task) queue.notify();
        }
    }
    
    public void cancel() {
        synchronized (queue) {
            thread.newTasksMayBeScheduled = false;
            queue.clear();
            queue.notify();
        }
    }
    
    public int purge() {
        int result = 0;
        synchronized (queue) {
            for (int i = queue.size(); i > 0; i--) {
                if (queue.get(i).state == TimerTask.CANCELLED) {
                    queue.quickRemove(i);
                    result++;
                }
            }
            if (result != 0) queue.heapify();
        }
        return result;
    }
}
