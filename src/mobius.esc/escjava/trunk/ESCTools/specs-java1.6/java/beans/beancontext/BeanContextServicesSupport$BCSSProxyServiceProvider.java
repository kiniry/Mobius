package java.beans.beancontext;

import java.util.Iterator;
import java.util.TooManyListenersException;

public class BeanContextServicesSupport$BCSSProxyServiceProvider implements BeanContextServiceProvider, BeanContextServiceRevokedListener {
    /*synthetic*/ final BeanContextServicesSupport this$0;
    
    BeanContextServicesSupport$BCSSProxyServiceProvider(/*synthetic*/ final BeanContextServicesSupport this$0, BeanContextServices bcs) {
        this.this$0 = this$0;
        
        nestingCtxt = bcs;
    }
    
    public Object getService(BeanContextServices bcs, Object requestor, Class serviceClass, Object serviceSelector) {
        Object service = null;
        try {
            service = nestingCtxt.getService(bcs, requestor, serviceClass, serviceSelector, this);
        } catch (TooManyListenersException tmle) {
            return null;
        }
        return service;
    }
    
    public void releaseService(BeanContextServices bcs, Object requestor, Object service) {
        nestingCtxt.releaseService(bcs, requestor, service);
    }
    
    public Iterator getCurrentServiceSelectors(BeanContextServices bcs, Class serviceClass) {
        return nestingCtxt.getCurrentServiceSelectors(serviceClass);
    }
    
    public void serviceRevoked(BeanContextServiceRevokedEvent bcsre) {
        Iterator i = this$0.bcsChildren();
        while (i.hasNext()) {
            ((BeanContextServicesSupport$BCSSChild)(BeanContextServicesSupport$BCSSChild)i.next()).revokeService(bcsre.getServiceClass(), true, bcsre.isCurrentServiceInvalidNow());
        }
    }
    private BeanContextServices nestingCtxt;
}
