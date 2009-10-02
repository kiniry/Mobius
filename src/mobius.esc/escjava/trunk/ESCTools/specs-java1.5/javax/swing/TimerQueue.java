package javax.swing;

import java.util.*;
import sun.awt.AppContext;

class TimerQueue implements Runnable {
    private static final Object sharedInstanceKey = new StringBuffer("TimerQueue.sharedInstanceKey");
    private static final Object expiredTimersKey = new StringBuffer("TimerQueue.expiredTimersKey");
    Timer firstTimer;
    boolean running;
    private static final Object classLock = new Object();
    
    public TimerQueue() {
        
        start();
    }
    
    public static TimerQueue sharedInstance() {
        synchronized (classLock) {
            TimerQueue sharedInst = (TimerQueue)(TimerQueue)SwingUtilities.appContextGet(sharedInstanceKey);
            if (sharedInst == null) {
                sharedInst = new TimerQueue();
                SwingUtilities.appContextPut(sharedInstanceKey, sharedInst);
            }
            return sharedInst;
        }
    }
    
    synchronized void start() {
        if (running) {
            throw new RuntimeException("Can\'t start a TimerQueue that is already running");
        } else {
            final ThreadGroup threadGroup = AppContext.getAppContext().getThreadGroup();
            java.security.AccessController.doPrivileged(new TimerQueue$1(this, threadGroup));
            running = true;
        }
    }
    
    synchronized void stop() {
        running = false;
        notify();
    }
    
    synchronized void addTimer(Timer timer, long expirationTime) {
        Timer previousTimer;
        Timer nextTimer;
        if (timer.running) {
            return;
        }
        previousTimer = null;
        nextTimer = firstTimer;
        while (nextTimer != null) {
            if (nextTimer.expirationTime > expirationTime) break;
            previousTimer = nextTimer;
            nextTimer = nextTimer.nextTimer;
        }
        if (previousTimer == null) {
            firstTimer = timer;
        } else {
            previousTimer.nextTimer = timer;
        }
        timer.expirationTime = expirationTime;
        timer.nextTimer = nextTimer;
        timer.running = true;
        notify();
    }
    
    synchronized void removeTimer(Timer timer) {
        Timer previousTimer;
        Timer nextTimer;
        boolean found;
        if (!timer.running) return;
        previousTimer = null;
        nextTimer = firstTimer;
        found = false;
        while (nextTimer != null) {
            if (nextTimer == timer) {
                found = true;
                break;
            }
            previousTimer = nextTimer;
            nextTimer = nextTimer.nextTimer;
        }
        if (!found) return;
        if (previousTimer == null) {
            firstTimer = timer.nextTimer;
        } else {
            previousTimer.nextTimer = timer.nextTimer;
        }
        timer.expirationTime = 0;
        timer.nextTimer = null;
        timer.running = false;
    }
    
    synchronized boolean containsTimer(Timer timer) {
        return timer.running;
    }
    
    synchronized long postExpiredTimers() {
        Timer timer;
        long currentTime;
        long timeToWait;
        do {
            timer = firstTimer;
            if (timer == null) return 0;
            currentTime = System.currentTimeMillis();
            timeToWait = timer.expirationTime - currentTime;
            if (timeToWait <= 0) {
                try {
                    timer.post();
                } catch (SecurityException e) {
                }
                removeTimer(timer);
                if (timer.isRepeats()) {
                    addTimer(timer, currentTime + timer.getDelay());
                }
                try {
                    wait(1);
                } catch (InterruptedException e) {
                }
            }
        }         while (timeToWait <= 0);
        return timeToWait;
    }
    
    public synchronized void run() {
        long timeToWait;
        try {
            while (running) {
                timeToWait = postExpiredTimers();
                try {
                    wait(timeToWait);
                } catch (InterruptedException e) {
                }
            }
        } catch (ThreadDeath td) {
            running = false;
            Timer timer = firstTimer;
            while (timer != null) {
                timer.cancelEvent();
                timer = timer.nextTimer;
            }
            SystemEventQueueUtilities.restartTimerQueueThread();
            throw td;
        }
    }
    
    public synchronized String toString() {
        StringBuffer buf;
        Timer nextTimer;
        buf = new StringBuffer();
        buf.append("TimerQueue (");
        nextTimer = firstTimer;
        while (nextTimer != null) {
            buf.append(nextTimer.toString());
            nextTimer = nextTimer.nextTimer;
            if (nextTimer != null) buf.append(", ");
        }
        buf.append(")");
        return buf.toString();
    }
}
