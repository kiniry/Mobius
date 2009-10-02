package java.beans;

import java.io.Serializable;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import sun.awt.EventListenerAggregate;

public class PropertyChangeSupport implements java.io.Serializable {
    private transient EventListenerAggregate listeners;
    
    public PropertyChangeSupport(Object sourceBean) {
        
        if (sourceBean == null) {
            throw new NullPointerException();
        }
        source = sourceBean;
    }
    
    public synchronized void addPropertyChangeListener(PropertyChangeListener listener) {
        if (listener == null) {
            return;
        }
        if (listener instanceof PropertyChangeListenerProxy) {
            PropertyChangeListenerProxy proxy = (PropertyChangeListenerProxy)(PropertyChangeListenerProxy)listener;
            addPropertyChangeListener(proxy.getPropertyName(), (PropertyChangeListener)(PropertyChangeListener)proxy.getListener());
        } else {
            if (listeners == null) {
                listeners = new EventListenerAggregate(PropertyChangeListener.class);
            }
            listeners.add(listener);
        }
    }
    
    public synchronized void removePropertyChangeListener(PropertyChangeListener listener) {
        if (listener == null) {
            return;
        }
        if (listener instanceof PropertyChangeListenerProxy) {
            PropertyChangeListenerProxy proxy = (PropertyChangeListenerProxy)(PropertyChangeListenerProxy)listener;
            removePropertyChangeListener(proxy.getPropertyName(), (PropertyChangeListener)(PropertyChangeListener)proxy.getListener());
        } else {
            if (listeners == null) {
                return;
            }
            listeners.remove(listener);
        }
    }
    
    public synchronized PropertyChangeListener[] getPropertyChangeListeners() {
        List returnList = new ArrayList();
        if (listeners != null) {
            returnList.addAll(Arrays.asList(listeners.getListenersInternal()));
        }
        if (children != null) {
            Iterator iterator = children.keySet().iterator();
            while (iterator.hasNext()) {
                String key = (String)(String)iterator.next();
                PropertyChangeSupport child = (PropertyChangeSupport)(PropertyChangeSupport)children.get(key);
                PropertyChangeListener[] childListeners = child.getPropertyChangeListeners();
                for (int index = childListeners.length - 1; index >= 0; index--) {
                    returnList.add(new PropertyChangeListenerProxy(key, childListeners[index]));
                }
            }
        }
        return (PropertyChangeListener[])((PropertyChangeListener[])returnList.toArray(new PropertyChangeListener[0]));
    }
    
    public synchronized void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        if (listener == null || propertyName == null) {
            return;
        }
        if (children == null) {
            children = new java.util.Hashtable();
        }
        PropertyChangeSupport child = (PropertyChangeSupport)(PropertyChangeSupport)children.get(propertyName);
        if (child == null) {
            child = new PropertyChangeSupport(source);
            children.put(propertyName, child);
        }
        child.addPropertyChangeListener(listener);
    }
    
    public synchronized void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        if (listener == null || propertyName == null) {
            return;
        }
        if (children == null) {
            return;
        }
        PropertyChangeSupport child = (PropertyChangeSupport)(PropertyChangeSupport)children.get(propertyName);
        if (child == null) {
            return;
        }
        child.removePropertyChangeListener(listener);
    }
    
    public synchronized PropertyChangeListener[] getPropertyChangeListeners(String propertyName) {
        ArrayList returnList = new ArrayList();
        if (children != null && propertyName != null) {
            PropertyChangeSupport support = (PropertyChangeSupport)(PropertyChangeSupport)children.get(propertyName);
            if (support != null) {
                returnList.addAll(Arrays.asList(support.getPropertyChangeListeners()));
            }
        }
        return (PropertyChangeListener[])((PropertyChangeListener[])returnList.toArray(new PropertyChangeListener[0]));
    }
    
    public void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
        if (oldValue != null && newValue != null && oldValue.equals(newValue)) {
            return;
        }
        firePropertyChange(new PropertyChangeEvent(source, propertyName, oldValue, newValue));
    }
    
    public void firePropertyChange(String propertyName, int oldValue, int newValue) {
        if (oldValue == newValue) {
            return;
        }
        firePropertyChange(propertyName, new Integer(oldValue), new Integer(newValue));
    }
    
    public void firePropertyChange(String propertyName, boolean oldValue, boolean newValue) {
        if (oldValue == newValue) {
            return;
        }
        firePropertyChange(propertyName, Boolean.valueOf(oldValue), Boolean.valueOf(newValue));
    }
    
    public void firePropertyChange(PropertyChangeEvent evt) {
        Object oldValue = evt.getOldValue();
        Object newValue = evt.getNewValue();
        String propertyName = evt.getPropertyName();
        if (oldValue != null && newValue != null && oldValue.equals(newValue)) {
            return;
        }
        if (listeners != null) {
            Object[] list = listeners.getListenersInternal();
            for (int i = 0; i < list.length; i++) {
                PropertyChangeListener target = (PropertyChangeListener)(PropertyChangeListener)list[i];
                target.propertyChange(evt);
            }
        }
        if (children != null && propertyName != null) {
            PropertyChangeSupport child = null;
            child = (PropertyChangeSupport)(PropertyChangeSupport)children.get(propertyName);
            if (child != null) {
                child.firePropertyChange(evt);
            }
        }
    }
    
    public void fireIndexedPropertyChange(String propertyName, int index, Object oldValue, Object newValue) {
        firePropertyChange(new IndexedPropertyChangeEvent(source, propertyName, oldValue, newValue, index));
    }
    
    public void fireIndexedPropertyChange(String propertyName, int index, int oldValue, int newValue) {
        if (oldValue == newValue) {
            return;
        }
        fireIndexedPropertyChange(propertyName, index, new Integer(oldValue), new Integer(newValue));
    }
    
    public void fireIndexedPropertyChange(String propertyName, int index, boolean oldValue, boolean newValue) {
        if (oldValue == newValue) {
            return;
        }
        fireIndexedPropertyChange(propertyName, index, Boolean.valueOf(oldValue), Boolean.valueOf(newValue));
    }
    
    public synchronized boolean hasListeners(String propertyName) {
        if (listeners != null && !listeners.isEmpty()) {
            return true;
        }
        if (children != null && propertyName != null) {
            PropertyChangeSupport child = (PropertyChangeSupport)(PropertyChangeSupport)children.get(propertyName);
            if (child != null && child.listeners != null) {
                return !child.listeners.isEmpty();
            }
        }
        return false;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if (listeners != null) {
            Object[] list = listeners.getListenersCopy();
            for (int i = 0; i < list.length; i++) {
                PropertyChangeListener l = (PropertyChangeListener)(PropertyChangeListener)list[i];
                if (l instanceof Serializable) {
                    s.writeObject(l);
                }
            }
        }
        s.writeObject(null);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        Object listenerOrNull;
        while (null != (listenerOrNull = s.readObject())) {
            addPropertyChangeListener((PropertyChangeListener)(PropertyChangeListener)listenerOrNull);
        }
    }
    private java.util.Hashtable children;
    private Object source;
    private int propertyChangeSupportSerializedDataVersion = 2;
    static final long serialVersionUID = 6401253773779951803L;
}
