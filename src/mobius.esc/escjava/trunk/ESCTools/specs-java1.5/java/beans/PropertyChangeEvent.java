package java.beans;

public class PropertyChangeEvent extends java.util.EventObject {
    
    public PropertyChangeEvent(Object source, String propertyName, Object oldValue, Object newValue) {
        super(source);
        this.propertyName = propertyName;
        this.newValue = newValue;
        this.oldValue = oldValue;
    }
    
    public String getPropertyName() {
        return propertyName;
    }
    
    public Object getNewValue() {
        return newValue;
    }
    
    public Object getOldValue() {
        return oldValue;
    }
    
    public void setPropagationId(Object propagationId) {
        this.propagationId = propagationId;
    }
    
    public Object getPropagationId() {
        return propagationId;
    }
    private String propertyName;
    private Object newValue;
    private Object oldValue;
    private Object propagationId;
}
