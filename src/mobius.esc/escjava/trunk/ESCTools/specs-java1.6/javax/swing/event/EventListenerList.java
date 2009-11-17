package javax.swing.event;

import java.io.*;
import java.util.*;
import java.lang.reflect.Array;

public class EventListenerList implements Serializable {
    
    public EventListenerList() {
        
    }
    private static final Object[] NULL_ARRAY = new Object[0];
    protected transient Object[] listenerList = NULL_ARRAY;
    
    public Object[] getListenerList() {
        return listenerList;
    }
    
    public EventListener[] getListeners(Class t) {
        Object[] lList = listenerList;
        int n = getListenerCount(lList, t);
        EventListener[] result = (EventListener[])(EventListener[])Array.newInstance(t, n);
        int j = 0;
        for (int i = lList.length - 2; i >= 0; i -= 2) {
            if (lList[i] == t) {
                result[j++] = (EventListener)(EventListener)lList[i + 1];
            }
        }
        return result;
    }
    
    public int getListenerCount() {
        return listenerList.length / 2;
    }
    
    public int getListenerCount(Class t) {
        Object[] lList = listenerList;
        return getListenerCount(lList, t);
    }
    
    private int getListenerCount(Object[] list, Class t) {
        int count = 0;
        for (int i = 0; i < list.length; i += 2) {
            if (t == (Class)(Class)list[i]) count++;
        }
        return count;
    }
    
    public synchronized void add(Class t, EventListener l) {
        if (l == null) {
            return;
        }
        if (!t.isInstance(l)) {
            throw new IllegalArgumentException("Listener " + l + " is not of type " + t);
        }
        if (listenerList == NULL_ARRAY) {
            listenerList = new Object[]{t, l};
        } else {
            int i = listenerList.length;
            Object[] tmp = new Object[i + 2];
            System.arraycopy(listenerList, 0, tmp, 0, i);
            tmp[i] = t;
            tmp[i + 1] = l;
            listenerList = tmp;
        }
    }
    
    public synchronized void remove(Class t, EventListener l) {
        if (l == null) {
            return;
        }
        if (!t.isInstance(l)) {
            throw new IllegalArgumentException("Listener " + l + " is not of type " + t);
        }
        int index = -1;
        for (int i = listenerList.length - 2; i >= 0; i -= 2) {
            if ((listenerList[i] == t) && (listenerList[i + 1].equals(l) == true)) {
                index = i;
                break;
            }
        }
        if (index != -1) {
            Object[] tmp = new Object[listenerList.length - 2];
            System.arraycopy(listenerList, 0, tmp, 0, index);
            if (index < tmp.length) System.arraycopy(listenerList, index + 2, tmp, index, tmp.length - index);
            listenerList = (tmp.length == 0) ? NULL_ARRAY : tmp;
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        Object[] lList = listenerList;
        s.defaultWriteObject();
        for (int i = 0; i < lList.length; i += 2) {
            Class t = (Class)(Class)lList[i];
            EventListener l = (EventListener)(EventListener)lList[i + 1];
            if ((l != null) && (l instanceof Serializable)) {
                s.writeObject(t.getName());
                s.writeObject(l);
            }
        }
        s.writeObject(null);
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        listenerList = NULL_ARRAY;
        s.defaultReadObject();
        Object listenerTypeOrNull;
        while (null != (listenerTypeOrNull = s.readObject())) {
            ClassLoader cl = Thread.currentThread().getContextClassLoader();
            EventListener l = (EventListener)(EventListener)s.readObject();
            add((Class)Class.forName((String)(String)listenerTypeOrNull, true, cl), l);
        }
    }
    
    public String toString() {
        Object[] lList = listenerList;
        String s = "EventListenerList: ";
        s += lList.length / 2 + " listeners: ";
        for (int i = 0; i <= lList.length - 2; i += 2) {
            s += " type " + ((Class)(Class)lList[i]).getName();
            s += " listener " + lList[i + 1];
        }
        return s;
    }
}
