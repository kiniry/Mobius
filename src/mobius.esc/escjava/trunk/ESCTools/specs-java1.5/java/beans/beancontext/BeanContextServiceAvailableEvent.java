package java.beans.beancontext;

import java.beans.beancontext.BeanContextEvent;
import java.beans.beancontext.BeanContextServices;
import java.util.Iterator;

public class BeanContextServiceAvailableEvent extends BeanContextEvent {
    
    public BeanContextServiceAvailableEvent(BeanContextServices bcs, Class sc) {
        super((BeanContext)bcs);
        serviceClass = sc;
    }
    
    public BeanContextServices getSourceAsBeanContextServices() {
        return (BeanContextServices)(BeanContextServices)getBeanContext();
    }
    
    public Class getServiceClass() {
        return serviceClass;
    }
    
    public Iterator getCurrentServiceSelectors() {
        return ((BeanContextServices)(BeanContextServices)getSource()).getCurrentServiceSelectors(serviceClass);
    }
    protected Class serviceClass;
}
