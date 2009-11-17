package java.beans;

public interface PropertyEditor {
    
    void setValue(Object value);
    
    Object getValue();
    
    boolean isPaintable();
    
    void paintValue(java.awt.Graphics gfx, java.awt.Rectangle box);
    
    String getJavaInitializationString();
    
    String getAsText();
    
    void setAsText(String text) throws java.lang.IllegalArgumentException;
    
    String[] getTags();
    
    java.awt.Component getCustomEditor();
    
    boolean supportsCustomEditor();
    
    void addPropertyChangeListener(PropertyChangeListener listener);
    
    void removePropertyChangeListener(PropertyChangeListener listener);
}
