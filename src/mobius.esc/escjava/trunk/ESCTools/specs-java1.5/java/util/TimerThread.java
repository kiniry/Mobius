package java.util;

class TimerThread extends Thread {
    boolean newTasksMayBeScheduled = true;
    private TaskQueue queue;
    
    TimerThread(TaskQueue queue) {
        
        this.queue = queue;
    }
    
    public void run() {
        try {
            mainLoop();
        } finally {
            synchronized (queue) {
                newTasksMayBeScheduled = false;
                queue.clear();
            }
        }
    }
    
    private void mainLoop() {
        while (true) {
            try {
                TimerTask task;
                boolean taskFired;
                synchronized (queue) {
                    while (queue.isEmpty() && newTasksMayBeScheduled) queue.wait();
                    if (queue.isEmpty()) break;
                    long currentTime;
                    long executionTime;
                    task = queue.getMin();
                    synchronized (task.lock) {
                        if (task.state == TimerTask.CANCELLED) {
                            queue.removeMin();
                            continue;
                        }
                        currentTime = System.currentTimeMillis();
                        executionTime = task.nextExecutionTime;
                        if (taskFired = (executionTime <= currentTime)) {
                            if (task.period == 0) {
                                queue.removeMin();
                                task.state = TimerTask.EXECUTED;
                            } else {
                                queue.rescheduleMin(task.period < 0 ? currentTime - task.period : executionTime + task.period);
                            }
                        }
                    }
                    if (!taskFired) queue.wait(executionTime - currentTime);
                }
                if (taskFired) task.run();
            } catch (InterruptedException e) {
            }
        }
    }
}
