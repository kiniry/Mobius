package java.beans;

public class PropertyVetoException extends Exception {
    
    public PropertyVetoException(String mess, PropertyChangeEvent evt) {
        super(mess);
        this.evt = evt;
    }
    
    public PropertyChangeEvent getPropertyChangeEvent() {
        return evt;
    }
    private PropertyChangeEvent evt;
}
