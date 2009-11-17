package java.beans;

import java.util.EventListenerProxy;

public class VetoableChangeListenerProxy extends EventListenerProxy implements VetoableChangeListener {
    private String propertyName;
    
    public VetoableChangeListenerProxy(String propertyName, VetoableChangeListener listener) {
        super(listener);
        this.propertyName = propertyName;
    }
    
    public void vetoableChange(PropertyChangeEvent evt) throws PropertyVetoException {
        ((VetoableChangeListener)(VetoableChangeListener)getListener()).vetoableChange(evt);
    }
    
    public String getPropertyName() {
        return propertyName;
    }
}
