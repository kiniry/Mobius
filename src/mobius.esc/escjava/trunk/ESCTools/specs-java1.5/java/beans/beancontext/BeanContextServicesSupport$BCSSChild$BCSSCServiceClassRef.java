package java.beans.beancontext;

import java.util.HashMap;
import java.util.Iterator;
import java.util.TooManyListenersException;

class BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef {
    /*synthetic*/ final BeanContextServicesSupport$BCSSChild this$1;
    
    BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef(/*synthetic*/ final BeanContextServicesSupport$BCSSChild this$1, Class sc, BeanContextServiceProvider bcsp, boolean delegated) {
        this.this$1 = this$1;
        
        serviceClass = sc;
        if (delegated) delegateProvider = bcsp; else serviceProvider = bcsp;
    }
    
    void addRequestor(Object requestor, BeanContextServiceRevokedListener bcsrl) throws TooManyListenersException {
        BeanContextServiceRevokedListener cbcsrl = (BeanContextServiceRevokedListener)(BeanContextServiceRevokedListener)requestors.get(requestor);
        if (cbcsrl != null && !cbcsrl.equals(bcsrl)) throw new TooManyListenersException();
        requestors.put(requestor, bcsrl);
    }
    
    void removeRequestor(Object requestor) {
        requestors.remove(requestor);
    }
    
    void verifyRequestor(Object requestor, BeanContextServiceRevokedListener bcsrl) throws TooManyListenersException {
        BeanContextServiceRevokedListener cbcsrl = (BeanContextServiceRevokedListener)(BeanContextServiceRevokedListener)requestors.get(requestor);
        if (cbcsrl != null && !cbcsrl.equals(bcsrl)) throw new TooManyListenersException();
    }
    
    void verifyAndMaybeSetProvider(BeanContextServiceProvider bcsp, boolean isDelegated) {
        BeanContextServiceProvider current;
        if (isDelegated) {
            current = delegateProvider;
            if (current == null || bcsp == null) {
                delegateProvider = bcsp;
                return;
            }
        } else {
            current = serviceProvider;
            if (current == null || bcsp == null) {
                serviceProvider = bcsp;
                return;
            }
        }
        if (!current.equals(bcsp)) throw new UnsupportedOperationException("existing service reference obtained from different BeanContextServiceProvider not supported");
    }
    
    Iterator cloneOfEntries() {
        return ((HashMap)(HashMap)requestors.clone()).entrySet().iterator();
    }
    
    Iterator entries() {
        return requestors.entrySet().iterator();
    }
    
    boolean isEmpty() {
        return requestors.isEmpty();
    }
    
    Class getServiceClass() {
        return serviceClass;
    }
    
    BeanContextServiceProvider getServiceProvider() {
        return serviceProvider;
    }
    
    BeanContextServiceProvider getDelegateProvider() {
        return delegateProvider;
    }
    
    boolean isDelegated() {
        return delegateProvider != null;
    }
    
    void addRef(boolean delegated) {
        if (delegated) {
            delegateRefs++;
        } else {
            serviceRefs++;
        }
    }
    
    void releaseRef(boolean delegated) {
        if (delegated) {
            if (--delegateRefs == 0) {
                delegateProvider = null;
            }
        } else {
            if (--serviceRefs <= 0) {
                serviceProvider = null;
            }
        }
    }
    
    int getRefs() {
        return serviceRefs + delegateRefs;
    }
    
    int getDelegateRefs() {
        return delegateRefs;
    }
    
    int getServiceRefs() {
        return serviceRefs;
    }
    Class serviceClass;
    BeanContextServiceProvider serviceProvider;
    int serviceRefs;
    BeanContextServiceProvider delegateProvider;
    int delegateRefs;
    HashMap requestors = new HashMap(1);
}
