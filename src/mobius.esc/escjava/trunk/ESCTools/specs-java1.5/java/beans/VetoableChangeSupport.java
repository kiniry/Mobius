package java.beans;

import java.io.Serializable;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class VetoableChangeSupport implements java.io.Serializable {
    
    public VetoableChangeSupport(Object sourceBean) {
        
        if (sourceBean == null) {
            throw new NullPointerException();
        }
        source = sourceBean;
    }
    
    public synchronized void addVetoableChangeListener(VetoableChangeListener listener) {
        if (listener == null) {
            return;
        }
        if (listener instanceof VetoableChangeListenerProxy) {
            VetoableChangeListenerProxy proxy = (VetoableChangeListenerProxy)(VetoableChangeListenerProxy)listener;
            addVetoableChangeListener(proxy.getPropertyName(), (VetoableChangeListener)(VetoableChangeListener)proxy.getListener());
        } else {
            if (listeners == null) {
                listeners = new java.util.Vector();
            }
        }
        listeners.addElement(listener);
    }
    
    public synchronized void removeVetoableChangeListener(VetoableChangeListener listener) {
        if (listener == null) {
            return;
        }
        if (listener instanceof VetoableChangeListenerProxy) {
            VetoableChangeListenerProxy proxy = (VetoableChangeListenerProxy)(VetoableChangeListenerProxy)listener;
            removeVetoableChangeListener(proxy.getPropertyName(), (VetoableChangeListener)(VetoableChangeListener)proxy.getListener());
        } else {
            if (listeners == null) {
                return;
            }
            listeners.removeElement(listener);
        }
    }
    
    public synchronized VetoableChangeListener[] getVetoableChangeListeners() {
        List returnList = new ArrayList();
        if (listeners != null) {
            returnList.addAll(listeners);
        }
        if (children != null) {
            Iterator iterator = children.keySet().iterator();
            while (iterator.hasNext()) {
                String key = (String)(String)iterator.next();
                VetoableChangeSupport child = (VetoableChangeSupport)(VetoableChangeSupport)children.get(key);
                VetoableChangeListener[] childListeners = child.getVetoableChangeListeners();
                for (int index = childListeners.length - 1; index >= 0; index--) {
                    returnList.add(new VetoableChangeListenerProxy(key, childListeners[index]));
                }
            }
        }
        return (VetoableChangeListener[])((VetoableChangeListener[])returnList.toArray(new VetoableChangeListener[0]));
    }
    
    public synchronized void addVetoableChangeListener(String propertyName, VetoableChangeListener listener) {
        if (listener == null || propertyName == null) {
            return;
        }
        if (children == null) {
            children = new java.util.Hashtable();
        }
        VetoableChangeSupport child = (VetoableChangeSupport)(VetoableChangeSupport)children.get(propertyName);
        if (child == null) {
            child = new VetoableChangeSupport(source);
            children.put(propertyName, child);
        }
        child.addVetoableChangeListener(listener);
    }
    
    public synchronized void removeVetoableChangeListener(String propertyName, VetoableChangeListener listener) {
        if (listener == null || propertyName == null) {
            return;
        }
        if (children == null) {
            return;
        }
        VetoableChangeSupport child = (VetoableChangeSupport)(VetoableChangeSupport)children.get(propertyName);
        if (child == null) {
            return;
        }
        child.removeVetoableChangeListener(listener);
    }
    
    public synchronized VetoableChangeListener[] getVetoableChangeListeners(String propertyName) {
        List returnList = new ArrayList();
        if (children != null && propertyName != null) {
            VetoableChangeSupport support = (VetoableChangeSupport)(VetoableChangeSupport)children.get(propertyName);
            if (support != null) {
                returnList.addAll(Arrays.asList(support.getVetoableChangeListeners()));
            }
        }
        return (VetoableChangeListener[])((VetoableChangeListener[])returnList.toArray(new VetoableChangeListener[0]));
    }
    
    public void fireVetoableChange(String propertyName, Object oldValue, Object newValue) throws PropertyVetoException {
        if (listeners == null && children == null) {
            return;
        }
        PropertyChangeEvent evt = new PropertyChangeEvent(source, propertyName, oldValue, newValue);
        fireVetoableChange(evt);
    }
    
    public void fireVetoableChange(String propertyName, int oldValue, int newValue) throws PropertyVetoException {
        if (oldValue == newValue) {
            return;
        }
        fireVetoableChange(propertyName, new Integer(oldValue), new Integer(newValue));
    }
    
    public void fireVetoableChange(String propertyName, boolean oldValue, boolean newValue) throws PropertyVetoException {
        if (oldValue == newValue) {
            return;
        }
        fireVetoableChange(propertyName, Boolean.valueOf(oldValue), Boolean.valueOf(newValue));
    }
    
    public void fireVetoableChange(PropertyChangeEvent evt) throws PropertyVetoException {
        Object oldValue = evt.getOldValue();
        Object newValue = evt.getNewValue();
        String propertyName = evt.getPropertyName();
        if (oldValue != null && newValue != null && oldValue.equals(newValue)) {
            return;
        }
        java.util.Vector targets = null;
        VetoableChangeSupport child = null;
        synchronized (this) {
            if (listeners != null) {
                targets = (java.util.Vector)(.java.util.Vector)listeners.clone();
            }
            if (children != null && propertyName != null) {
                child = (VetoableChangeSupport)(VetoableChangeSupport)children.get(propertyName);
            }
        }
        if (listeners != null) {
            try {
                for (int i = 0; i < targets.size(); i++) {
                    VetoableChangeListener target = (VetoableChangeListener)(VetoableChangeListener)targets.elementAt(i);
                    target.vetoableChange(evt);
                }
            } catch (PropertyVetoException veto) {
                evt = new PropertyChangeEvent(source, propertyName, newValue, oldValue);
                for (int i = 0; i < targets.size(); i++) {
                    try {
                        VetoableChangeListener target = (VetoableChangeListener)(VetoableChangeListener)targets.elementAt(i);
                        target.vetoableChange(evt);
                    } catch (PropertyVetoException ex) {
                    }
                }
                throw veto;
            }
        }
        if (child != null) {
            child.fireVetoableChange(evt);
        }
    }
    
    public synchronized boolean hasListeners(String propertyName) {
        if (listeners != null && !listeners.isEmpty()) {
            return true;
        }
        if (children != null && propertyName != null) {
            VetoableChangeSupport child = (VetoableChangeSupport)(VetoableChangeSupport)children.get(propertyName);
            if (child != null && child.listeners != null) {
                return !child.listeners.isEmpty();
            }
        }
        return false;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        java.util.Vector v = null;
        synchronized (this) {
            if (listeners != null) {
                v = (java.util.Vector)(.java.util.Vector)listeners.clone();
            }
        }
        if (v != null) {
            for (int i = 0; i < v.size(); i++) {
                VetoableChangeListener l = (VetoableChangeListener)(VetoableChangeListener)v.elementAt(i);
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
            addVetoableChangeListener((VetoableChangeListener)(VetoableChangeListener)listenerOrNull);
        }
    }
    private transient java.util.Vector listeners;
    private java.util.Hashtable children;
    private Object source;
    private int vetoableChangeSupportSerializedDataVersion = 2;
    static final long serialVersionUID = -5090210921595982017L;
}
