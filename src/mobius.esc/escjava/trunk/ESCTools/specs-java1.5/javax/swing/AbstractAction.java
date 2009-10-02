package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.Serializable;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import javax.swing.event.SwingPropertyChangeSupport;

public abstract class AbstractAction implements Action, Cloneable, Serializable {
    protected boolean enabled = true;
    private transient ArrayTable arrayTable;
    
    public AbstractAction() {
        
    }
    
    public AbstractAction(String name) {
        
        putValue(Action.NAME, name);
    }
    
    public AbstractAction(String name, Icon icon) {
        this(name);
        putValue(Action.SMALL_ICON, icon);
    }
    
    public Object getValue(String key) {
        if (arrayTable == null) {
            return null;
        }
        return arrayTable.get(key);
    }
    
    public void putValue(String key, Object newValue) {
        Object oldValue = null;
        if (arrayTable == null) {
            arrayTable = new ArrayTable();
        }
        if (arrayTable.containsKey(key)) oldValue = arrayTable.get(key);
        if (newValue == null) {
            arrayTable.remove(key);
        } else {
            arrayTable.put(key, newValue);
        }
        firePropertyChange(key, oldValue, newValue);
    }
    
    public boolean isEnabled() {
        return enabled;
    }
    
    public void setEnabled(boolean newValue) {
        boolean oldValue = this.enabled;
        if (oldValue != newValue) {
            this.enabled = newValue;
            firePropertyChange("enabled", Boolean.valueOf(oldValue), Boolean.valueOf(newValue));
        }
    }
    
    public Object[] getKeys() {
        if (arrayTable == null) {
            return null;
        }
        Object[] keys = new Object[arrayTable.size()];
        arrayTable.getKeys(keys);
        return keys;
    }
    protected SwingPropertyChangeSupport changeSupport;
    
    protected void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
        if (changeSupport == null || (oldValue != null && newValue != null && oldValue.equals(newValue))) {
            return;
        }
        changeSupport.firePropertyChange(propertyName, oldValue, newValue);
    }
    
    public synchronized void addPropertyChangeListener(PropertyChangeListener listener) {
        if (changeSupport == null) {
            changeSupport = new SwingPropertyChangeSupport(this);
        }
        changeSupport.addPropertyChangeListener(listener);
    }
    
    public synchronized void removePropertyChangeListener(PropertyChangeListener listener) {
        if (changeSupport == null) {
            return;
        }
        changeSupport.removePropertyChangeListener(listener);
    }
    
    public synchronized PropertyChangeListener[] getPropertyChangeListeners() {
        if (changeSupport == null) {
            return new PropertyChangeListener[0];
        }
        return changeSupport.getPropertyChangeListeners();
    }
    
    protected Object clone() throws CloneNotSupportedException {
        AbstractAction newAction = (AbstractAction)(AbstractAction)super.clone();
        synchronized (this) {
            if (arrayTable != null) {
                newAction.arrayTable = (ArrayTable)(ArrayTable)arrayTable.clone();
            }
        }
        return newAction;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        ArrayTable.writeArrayTable(s, arrayTable);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        for (int counter = s.readInt() - 1; counter >= 0; counter--) {
            putValue((String)(String)s.readObject(), s.readObject());
        }
    }
}
