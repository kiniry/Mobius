package java.beans;

public interface Customizer {
    
    void setObject(Object bean);
    
    void addPropertyChangeListener(PropertyChangeListener listener);
    
    void removePropertyChangeListener(PropertyChangeListener listener);
}
