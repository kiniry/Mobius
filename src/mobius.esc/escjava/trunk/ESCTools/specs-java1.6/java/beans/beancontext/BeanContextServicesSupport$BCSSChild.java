package java.beans.beancontext;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TooManyListenersException;

public class BeanContextServicesSupport$BCSSChild extends BeanContextSupport$BCSChild {
    /*synthetic*/ final BeanContextServicesSupport this$0;
    private static final long serialVersionUID = -3263851306889194873L;
    {
    }
    {
    }
    
    BeanContextServicesSupport$BCSSChild(/*synthetic*/ final BeanContextServicesSupport this$0, Object bcc, Object pee) {
        super(this$0, bcc, pee);
	this.this$0 = this$0;

    }
    
    synchronized void usingService(Object requestor, Object service, Class serviceClass, BeanContextServiceProvider bcsp, boolean isDelegated, BeanContextServiceRevokedListener bcsrl) throws TooManyListenersException, UnsupportedOperationException {
        BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef serviceClassRef = null;
        if (serviceClasses == null) serviceClasses = new HashMap(1); else serviceClassRef = (BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef)(BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef)serviceClasses.get(serviceClass);
        if (serviceClassRef == null) {
            serviceClassRef = new BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef(this, serviceClass, bcsp, isDelegated);
            serviceClasses.put(serviceClass, serviceClassRef);
        } else {
            serviceClassRef.verifyAndMaybeSetProvider(bcsp, isDelegated);
            serviceClassRef.verifyRequestor(requestor, bcsrl);
        }
        serviceClassRef.addRequestor(requestor, bcsrl);
        serviceClassRef.addRef(isDelegated);
        BeanContextServicesSupport$BCSSChild$BCSSCServiceRef serviceRef = null;
        Map services = null;
        if (serviceRequestors == null) {
            serviceRequestors = new HashMap(1);
        } else {
            services = (Map)(Map)serviceRequestors.get(requestor);
        }
        if (services == null) {
            services = new HashMap(1);
            serviceRequestors.put(requestor, services);
        } else serviceRef = (BeanContextServicesSupport$BCSSChild$BCSSCServiceRef)(BeanContextServicesSupport$BCSSChild$BCSSCServiceRef)services.get(service);
        if (serviceRef == null) {
            serviceRef = new BeanContextServicesSupport$BCSSChild$BCSSCServiceRef(this, serviceClassRef, isDelegated);
            services.put(service, serviceRef);
        } else {
            serviceRef.addRef();
        }
    }
    
    synchronized void releaseService(Object requestor, Object service) {
        if (serviceRequestors == null) return;
        Map services = (Map)(Map)serviceRequestors.get(requestor);
        if (services == null) return;
        BeanContextServicesSupport$BCSSChild$BCSSCServiceRef serviceRef = (BeanContextServicesSupport$BCSSChild$BCSSCServiceRef)(BeanContextServicesSupport$BCSSChild$BCSSCServiceRef)services.get(service);
        if (serviceRef == null) return;
        BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef serviceClassRef = serviceRef.getServiceClassRef();
        boolean isDelegated = serviceRef.isDelegated();
        BeanContextServiceProvider bcsp = isDelegated ? serviceClassRef.getDelegateProvider() : serviceClassRef.getServiceProvider();
        bcsp.releaseService(this$0.getBeanContextServicesPeer(), requestor, service);
        serviceClassRef.releaseRef(isDelegated);
        serviceClassRef.removeRequestor(requestor);
        if (serviceRef.release() == 0) {
            services.remove(service);
            if (services.isEmpty()) {
                serviceRequestors.remove(requestor);
                serviceClassRef.removeRequestor(requestor);
            }
            if (serviceRequestors.isEmpty()) {
                serviceRequestors = null;
            }
            if (serviceClassRef.isEmpty()) {
                serviceClasses.remove(serviceClassRef.getServiceClass());
            }
            if (serviceClasses.isEmpty()) serviceClasses = null;
        }
    }
    
    synchronized void revokeService(Class serviceClass, boolean isDelegated, boolean revokeNow) {
        if (serviceClasses == null) return;
        BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef serviceClassRef = (BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef)(BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef)serviceClasses.get(serviceClass);
        if (serviceClassRef == null) return;
        Iterator i = serviceClassRef.cloneOfEntries();
        BeanContextServiceRevokedEvent bcsre = new BeanContextServiceRevokedEvent(this$0.getBeanContextServicesPeer(), serviceClass, revokeNow);
        boolean noMoreRefs = false;
        while (i.hasNext() && serviceRequestors != null) {
            Map$Entry entry = (Map$Entry)(Map$Entry)i.next();
            BeanContextServiceRevokedListener listener = (BeanContextServiceRevokedListener)(BeanContextServiceRevokedListener)entry.getValue();
            if (revokeNow) {
                Object requestor = entry.getKey();
                Map services = (Map)(Map)serviceRequestors.get(requestor);
                if (services != null) {
                    Iterator i1 = services.entrySet().iterator();
                    while (i1.hasNext()) {
                        Map$Entry tmp = (Map$Entry)(Map$Entry)i1.next();
                        BeanContextServicesSupport$BCSSChild$BCSSCServiceRef serviceRef = (BeanContextServicesSupport$BCSSChild$BCSSCServiceRef)(BeanContextServicesSupport$BCSSChild$BCSSCServiceRef)tmp.getValue();
                        if (serviceRef.getServiceClassRef().equals(serviceClassRef) && isDelegated == serviceRef.isDelegated()) {
                            i1.remove();
                        }
                    }
                    if (noMoreRefs = services.isEmpty()) {
                        serviceRequestors.remove(requestor);
                    }
                }
                if (noMoreRefs) serviceClassRef.removeRequestor(requestor);
            }
            listener.serviceRevoked(bcsre);
        }
        if (revokeNow && serviceClasses != null) {
            if (serviceClassRef.isEmpty()) serviceClasses.remove(serviceClass);
            if (serviceClasses.isEmpty()) serviceClasses = null;
        }
        if (serviceRequestors != null && serviceRequestors.isEmpty()) serviceRequestors = null;
    }
    
    void cleanupReferences() {
        if (serviceRequestors == null) return;
        Iterator requestors = serviceRequestors.entrySet().iterator();
        while (requestors.hasNext()) {
            Map$Entry tmp = (Map$Entry)(Map$Entry)requestors.next();
            Object requestor = tmp.getKey();
            Iterator services = ((Map)(Map)tmp.getValue()).entrySet().iterator();
            requestors.remove();
            while (services.hasNext()) {
                Map$Entry entry = (Map$Entry)(Map$Entry)services.next();
                Object service = entry.getKey();
                BeanContextServicesSupport$BCSSChild$BCSSCServiceRef sref = (BeanContextServicesSupport$BCSSChild$BCSSCServiceRef)(BeanContextServicesSupport$BCSSChild$BCSSCServiceRef)entry.getValue();
                BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef scref = sref.getServiceClassRef();
                BeanContextServiceProvider bcsp = sref.isDelegated() ? scref.getDelegateProvider() : scref.getServiceProvider();
                scref.removeRequestor(requestor);
                services.remove();
                while (sref.release() >= 0) {
                    bcsp.releaseService(this$0.getBeanContextServicesPeer(), requestor, service);
                }
            }
        }
        serviceRequestors = null;
        serviceClasses = null;
    }
    
    void revokeAllDelegatedServicesNow() {
        if (serviceClasses == null) return;
        Iterator serviceClassRefs = new HashSet(serviceClasses.values()).iterator();
        while (serviceClassRefs.hasNext()) {
            BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef serviceClassRef = (BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef)(BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef)serviceClassRefs.next();
            if (!serviceClassRef.isDelegated()) continue;
            Iterator i = serviceClassRef.cloneOfEntries();
            BeanContextServiceRevokedEvent bcsre = new BeanContextServiceRevokedEvent(this$0.getBeanContextServicesPeer(), serviceClassRef.getServiceClass(), true);
            boolean noMoreRefs = false;
            while (i.hasNext()) {
                Map$Entry entry = (Map$Entry)(Map$Entry)i.next();
                BeanContextServiceRevokedListener listener = (BeanContextServiceRevokedListener)(BeanContextServiceRevokedListener)entry.getValue();
                Object requestor = entry.getKey();
                Map services = (Map)(Map)serviceRequestors.get(requestor);
                if (services != null) {
                    Iterator i1 = services.entrySet().iterator();
                    while (i1.hasNext()) {
                        Map$Entry tmp = (Map$Entry)(Map$Entry)i1.next();
                        BeanContextServicesSupport$BCSSChild$BCSSCServiceRef serviceRef = (BeanContextServicesSupport$BCSSChild$BCSSCServiceRef)(BeanContextServicesSupport$BCSSChild$BCSSCServiceRef)tmp.getValue();
                        if (serviceRef.getServiceClassRef().equals(serviceClassRef) && serviceRef.isDelegated()) {
                            i1.remove();
                        }
                    }
                    if (noMoreRefs = services.isEmpty()) {
                        serviceRequestors.remove(requestor);
                    }
                }
                if (noMoreRefs) serviceClassRef.removeRequestor(requestor);
                listener.serviceRevoked(bcsre);
                if (serviceClassRef.isEmpty()) serviceClasses.remove(serviceClassRef.getServiceClass());
            }
        }
        if (serviceClasses.isEmpty()) serviceClasses = null;
        if (serviceRequestors != null && serviceRequestors.isEmpty()) serviceRequestors = null;
    }
    private transient HashMap serviceClasses;
    private transient HashMap serviceRequestors;
}
