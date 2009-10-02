package java.beans.beancontext;

import java.util.Iterator;
import java.util.TooManyListenersException;
import java.beans.beancontext.BeanContext;
import java.beans.beancontext.BeanContextServiceProvider;
import java.beans.beancontext.BeanContextServicesListener;

public interface BeanContextServices extends BeanContext, BeanContextServicesListener {
    
    boolean addService(Class serviceClass, BeanContextServiceProvider serviceProvider);
    
    void revokeService(Class serviceClass, BeanContextServiceProvider serviceProvider, boolean revokeCurrentServicesNow);
    
    boolean hasService(Class serviceClass);
    
    Object getService(BeanContextChild child, Object requestor, Class serviceClass, Object serviceSelector, BeanContextServiceRevokedListener bcsrl) throws TooManyListenersException;
    
    void releaseService(BeanContextChild child, Object requestor, Object service);
    
    Iterator getCurrentServiceClasses();
    
    Iterator getCurrentServiceSelectors(Class serviceClass);
    
    void addBeanContextServicesListener(BeanContextServicesListener bcsl);
    
    void removeBeanContextServicesListener(BeanContextServicesListener bcsl);
}
