package java.beans;

public class PropertyChangeListenerProxy extends java.util.EventListenerProxy implements PropertyChangeListener {
    private String propertyName;
    
    public PropertyChangeListenerProxy(String propertyName, PropertyChangeListener listener) {
        super(listener);
        this.propertyName = propertyName;
    }
    
    public void propertyChange(PropertyChangeEvent evt) {
        ((PropertyChangeListener)(PropertyChangeListener)getListener()).propertyChange(evt);
    }
    
    public String getPropertyName() {
        return propertyName;
    }
}
