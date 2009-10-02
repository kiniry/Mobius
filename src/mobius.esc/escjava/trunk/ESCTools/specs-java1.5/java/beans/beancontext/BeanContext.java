package java.beans.beancontext;

import java.beans.DesignMode;
import java.beans.Visibility;
import java.io.InputStream;
import java.io.IOException;
import java.net.URL;
import java.util.Collection;

public interface BeanContext extends BeanContextChild, Collection, DesignMode, Visibility {
    
    Object instantiateChild(String beanName) throws IOException, ClassNotFoundException;
    
    InputStream getResourceAsStream(String name, BeanContextChild bcc) throws IllegalArgumentException;
    
    URL getResource(String name, BeanContextChild bcc) throws IllegalArgumentException;
    
    void addBeanContextMembershipListener(BeanContextMembershipListener bcml);
    
    void removeBeanContextMembershipListener(BeanContextMembershipListener bcml);
    public static final Object globalHierarchyLock = new Object();
}
