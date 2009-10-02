package java.beans;

public interface VetoableChangeListener extends java.util.EventListener {
    
    void vetoableChange(PropertyChangeEvent evt) throws PropertyVetoException;
}
