package java.beans.beancontext;

import java.beans.PropertyChangeListener;
import java.beans.VetoableChangeListener;
import java.beans.PropertyVetoException;
import java.beans.beancontext.BeanContext;

public interface BeanContextChild {
    
    void setBeanContext(BeanContext bc) throws PropertyVetoException;
    
    BeanContext getBeanContext();
    
    void addPropertyChangeListener(String name, PropertyChangeListener pcl);
    
    void removePropertyChangeListener(String name, PropertyChangeListener pcl);
    
    void addVetoableChangeListener(String name, VetoableChangeListener vcl);
    
    void removeVetoableChangeListener(String name, VetoableChangeListener vcl);
}
