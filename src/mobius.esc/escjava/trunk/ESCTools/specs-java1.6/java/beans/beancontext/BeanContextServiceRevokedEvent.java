package java.beans.beancontext;

import java.beans.beancontext.BeanContextEvent;
import java.beans.beancontext.BeanContextServices;

public class BeanContextServiceRevokedEvent extends BeanContextEvent {
    
    public BeanContextServiceRevokedEvent(BeanContextServices bcs, Class sc, boolean invalidate) {
        super((BeanContext)bcs);
        serviceClass = sc;
        invalidateRefs = invalidate;
    }
    
    public BeanContextServices getSourceAsBeanContextServices() {
        return (BeanContextServices)(BeanContextServices)getBeanContext();
    }
    
    public Class getServiceClass() {
        return serviceClass;
    }
    
    public boolean isServiceClass(Class service) {
        return serviceClass.equals(service);
    }
    
    public boolean isCurrentServiceInvalidNow() {
        return invalidateRefs;
    }
    protected Class serviceClass;
    private boolean invalidateRefs;
}
