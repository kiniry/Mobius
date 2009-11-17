package javax.swing;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import java.io.Serializable;
import javax.swing.event.EventListenerList;

public class Timer implements Serializable {
    
    /*synthetic*/ static boolean access$100(Timer x0) {
        return x0.notify;
    }
    
    /*synthetic*/ static boolean access$000() {
        return logTimers;
    }
    protected EventListenerList listenerList = new EventListenerList();
    private boolean notify = false;
    int initialDelay;
    int delay;
    boolean repeats = true;
    boolean coalesce = true;
    Runnable doPostEvent = null;
    private static boolean logTimers;
    long expirationTime;
    Timer nextTimer;
    boolean running;
    
    public Timer(int delay, ActionListener listener) {
        
        this.delay = delay;
        this.initialDelay = delay;
        doPostEvent = new Timer$DoPostEvent(this);
        if (listener != null) {
            addActionListener(listener);
        }
    }
    {
    }
    
    public void addActionListener(ActionListener listener) {
        listenerList.add(ActionListener.class, listener);
    }
    
    public void removeActionListener(ActionListener listener) {
        listenerList.remove(ActionListener.class, listener);
    }
    
    public ActionListener[] getActionListeners() {
        return (ActionListener[])(ActionListener[])listenerList.getListeners(ActionListener.class);
    }
    
    protected void fireActionPerformed(ActionEvent e) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ActionListener.class) {
                ((ActionListener)(ActionListener)listeners[i + 1]).actionPerformed(e);
            }
        }
    }
    
    public EventListener[] getListeners(Class listenerType) {
        return listenerList.getListeners(listenerType);
    }
    
    TimerQueue timerQueue() {
        return TimerQueue.sharedInstance();
    }
    
    public static void setLogTimers(boolean flag) {
        logTimers = flag;
    }
    
    public static boolean getLogTimers() {
        return logTimers;
    }
    
    public void setDelay(int delay) {
        if (delay < 0) {
            throw new IllegalArgumentException("Invalid delay: " + delay);
        } else {
            this.delay = delay;
        }
    }
    
    public int getDelay() {
        return delay;
    }
    
    public void setInitialDelay(int initialDelay) {
        if (initialDelay < 0) {
            throw new IllegalArgumentException("Invalid initial delay: " + initialDelay);
        } else {
            this.initialDelay = initialDelay;
        }
    }
    
    public int getInitialDelay() {
        return initialDelay;
    }
    
    public void setRepeats(boolean flag) {
        repeats = flag;
    }
    
    public boolean isRepeats() {
        return repeats;
    }
    
    public void setCoalesce(boolean flag) {
        boolean old = coalesce;
        coalesce = flag;
        if (!old && coalesce) {
            cancelEvent();
        }
    }
    
    public boolean isCoalesce() {
        return coalesce;
    }
    
    public void start() {
        timerQueue().addTimer(this, System.currentTimeMillis() + getInitialDelay());
    }
    
    public boolean isRunning() {
        return timerQueue().containsTimer(this);
    }
    
    public void stop() {
        timerQueue().removeTimer(this);
        cancelEvent();
    }
    
    public void restart() {
        stop();
        start();
    }
    
    synchronized void cancelEvent() {
        notify = false;
    }
    
    synchronized void post() {
        if (notify == false || !coalesce) {
            notify = true;
            SwingUtilities.invokeLater(doPostEvent);
        }
    }
}
