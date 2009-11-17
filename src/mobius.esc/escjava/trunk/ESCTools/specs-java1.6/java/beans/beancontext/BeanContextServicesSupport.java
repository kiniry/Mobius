package java.beans.beancontext;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map.Entry;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.TooManyListenersException;
import java.util.Locale;

public class BeanContextServicesSupport extends BeanContextSupport implements BeanContextServices {
    
    public BeanContextServicesSupport(BeanContextServices pee, Locale lcle, boolean dTime, boolean visible) {
        super(pee, lcle, dTime, visible);
    }
    
    public BeanContextServicesSupport(BeanContextServices pee, Locale lcle, boolean dtime) {
        this(pee, lcle, dtime, true);
    }
    
    public BeanContextServicesSupport(BeanContextServices pee, Locale lcle) {
        this(pee, lcle, false, true);
    }
    
    public BeanContextServicesSupport(BeanContextServices pee) {
        this(pee, null, false, true);
    }
    
    public BeanContextServicesSupport() {
        this(null, null, false, true);
    }
    
    public void initialize() {
        super.initialize();
        services = new HashMap(serializable + 1);
        bcsListeners = new ArrayList(1);
    }
    
    public BeanContextServices getBeanContextServicesPeer() {
        return (BeanContextServices)(BeanContextServices)getBeanContextChildPeer();
    }
    {
    }
    
    protected BeanContextSupport$BCSChild createBCSChild(Object targetChild, Object pee) {
        return new BeanContextServicesSupport$BCSSChild(this, targetChild, pee);
    }
    {
    }
    
    protected BeanContextServicesSupport$BCSSServiceProvider createBCSSServiceProvider(Class sc, BeanContextServiceProvider bcsp) {
        return new BeanContextServicesSupport$BCSSServiceProvider(sc, bcsp);
    }
    
    public void addBeanContextServicesListener(BeanContextServicesListener bcsl) {
        if (bcsl == null) throw new NullPointerException("bcsl");
        synchronized (bcsListeners) {
            if (bcsListeners.contains(bcsl)) return; else bcsListeners.add(bcsl);
        }
    }
    
    public void removeBeanContextServicesListener(BeanContextServicesListener bcsl) {
        if (bcsl == null) throw new NullPointerException("bcsl");
        synchronized (bcsListeners) {
            if (!bcsListeners.contains(bcsl)) return; else bcsListeners.remove(bcsl);
        }
    }
    
    public boolean addService(Class serviceClass, BeanContextServiceProvider bcsp) {
        return addService(serviceClass, bcsp, true);
    }
    
    protected boolean addService(Class serviceClass, BeanContextServiceProvider bcsp, boolean fireEvent) {
        if (serviceClass == null) throw new NullPointerException("serviceClass");
        if (bcsp == null) throw new NullPointerException("bcsp");
        synchronized (BeanContext.globalHierarchyLock) {
            if (services.containsKey(serviceClass)) return false; else {
                services.put(serviceClass, createBCSSServiceProvider(serviceClass, bcsp));
                if (bcsp instanceof Serializable) serializable++;
                if (!fireEvent) return true;
                BeanContextServiceAvailableEvent bcssae = new BeanContextServiceAvailableEvent(getBeanContextServicesPeer(), serviceClass);
                fireServiceAdded(bcssae);
                synchronized (children) {
                    Iterator i = children.keySet().iterator();
                    while (i.hasNext()) {
                        Object c = i.next();
                        if (c instanceof BeanContextServices) {
                            ((BeanContextServicesListener)(BeanContextServicesListener)c).serviceAvailable(bcssae);
                        }
                    }
                }
                return true;
            }
        }
    }
    
    public void revokeService(Class serviceClass, BeanContextServiceProvider bcsp, boolean revokeCurrentServicesNow) {
        if (serviceClass == null) throw new NullPointerException("serviceClass");
        if (bcsp == null) throw new NullPointerException("bcsp");
        synchronized (BeanContext.globalHierarchyLock) {
            if (!services.containsKey(serviceClass)) return;
            BeanContextServicesSupport$BCSSServiceProvider bcsssp = (BeanContextServicesSupport$BCSSServiceProvider)(BeanContextServicesSupport$BCSSServiceProvider)services.get(serviceClass);
            if (!bcsssp.getServiceProvider().equals(bcsp)) throw new IllegalArgumentException("service provider mismatch");
            services.remove(serviceClass);
            if (bcsp instanceof Serializable) serializable--;
            Iterator i = bcsChildren();
            while (i.hasNext()) {
                ((BeanContextServicesSupport$BCSSChild)(BeanContextServicesSupport$BCSSChild)i.next()).revokeService(serviceClass, false, revokeCurrentServicesNow);
            }
            fireServiceRevoked(serviceClass, revokeCurrentServicesNow);
        }
    }
    
    public synchronized boolean hasService(Class serviceClass) {
        if (serviceClass == null) throw new NullPointerException("serviceClass");
        synchronized (BeanContext.globalHierarchyLock) {
            if (services.containsKey(serviceClass)) return true;
            BeanContextServices bcs = null;
            try {
                bcs = (BeanContextServices)(BeanContextServices)getBeanContext();
            } catch (ClassCastException cce) {
                return false;
            }
            return bcs == null ? false : bcs.hasService(serviceClass);
        }
    }
    {
    }
    
    public Object getService(BeanContextChild child, Object requestor, Class serviceClass, Object serviceSelector, BeanContextServiceRevokedListener bcsrl) throws TooManyListenersException {
        if (child == null) throw new NullPointerException("child");
        if (serviceClass == null) throw new NullPointerException("serviceClass");
        if (requestor == null) throw new NullPointerException("requestor");
        if (bcsrl == null) throw new NullPointerException("bcsrl");
        Object service = null;
        BeanContextServicesSupport$BCSSChild bcsc;
        BeanContextServices bcssp = getBeanContextServicesPeer();
        synchronized (BeanContext.globalHierarchyLock) {
            synchronized (children) {
                bcsc = (BeanContextServicesSupport$BCSSChild)(BeanContextServicesSupport$BCSSChild)children.get(child);
            }
            if (bcsc == null) throw new IllegalArgumentException("not a child of this context");
            BeanContextServicesSupport$BCSSServiceProvider bcsssp = (BeanContextServicesSupport$BCSSServiceProvider)(BeanContextServicesSupport$BCSSServiceProvider)services.get(serviceClass);
            if (bcsssp != null) {
                BeanContextServiceProvider bcsp = bcsssp.getServiceProvider();
                service = bcsp.getService(bcssp, requestor, serviceClass, serviceSelector);
                if (service != null) {
                    try {
                        bcsc.usingService(requestor, service, serviceClass, bcsp, false, bcsrl);
                    } catch (TooManyListenersException tmle) {
                        bcsp.releaseService(bcssp, requestor, service);
                        throw tmle;
                    } catch (UnsupportedOperationException uope) {
                        bcsp.releaseService(bcssp, requestor, service);
                        throw uope;
                    }
                    return service;
                }
            }
            if (proxy != null) {
                service = proxy.getService(bcssp, requestor, serviceClass, serviceSelector);
                if (service != null) {
                    try {
                        bcsc.usingService(requestor, service, serviceClass, proxy, true, bcsrl);
                    } catch (TooManyListenersException tmle) {
                        proxy.releaseService(bcssp, requestor, service);
                        throw tmle;
                    } catch (UnsupportedOperationException uope) {
                        proxy.releaseService(bcssp, requestor, service);
                        throw uope;
                    }
                    return service;
                }
            }
        }
        return null;
    }
    
    public void releaseService(BeanContextChild child, Object requestor, Object service) {
        if (child == null) throw new NullPointerException("child");
        if (requestor == null) throw new NullPointerException("requestor");
        if (service == null) throw new NullPointerException("service");
        BeanContextServicesSupport$BCSSChild bcsc;
        synchronized (BeanContext.globalHierarchyLock) {
            synchronized (children) {
                bcsc = (BeanContextServicesSupport$BCSSChild)(BeanContextServicesSupport$BCSSChild)children.get(child);
            }
            if (bcsc != null) bcsc.releaseService(requestor, service); else throw new IllegalArgumentException("child actual is not a child of this BeanContext");
        }
    }
    
    public Iterator getCurrentServiceClasses() {
        return new BeanContextSupport$BCSIterator(services.keySet().iterator());
    }
    
    public Iterator getCurrentServiceSelectors(Class serviceClass) {
        BeanContextServicesSupport$BCSSServiceProvider bcsssp = (BeanContextServicesSupport$BCSSServiceProvider)(BeanContextServicesSupport$BCSSServiceProvider)services.get(serviceClass);
        return bcsssp != null ? new BeanContextSupport$BCSIterator(bcsssp.getServiceProvider().getCurrentServiceSelectors(getBeanContextServicesPeer(), serviceClass)) : null;
    }
    
    public void serviceAvailable(BeanContextServiceAvailableEvent bcssae) {
        synchronized (BeanContext.globalHierarchyLock) {
            if (services.containsKey(bcssae.getServiceClass())) return;
            fireServiceAdded(bcssae);
            Iterator i;
            synchronized (children) {
                i = children.keySet().iterator();
            }
            while (i.hasNext()) {
                Object c = i.next();
                if (c instanceof BeanContextServices) {
                    ((BeanContextServicesListener)(BeanContextServicesListener)c).serviceAvailable(bcssae);
                }
            }
        }
    }
    
    public void serviceRevoked(BeanContextServiceRevokedEvent bcssre) {
        synchronized (BeanContext.globalHierarchyLock) {
            if (services.containsKey(bcssre.getServiceClass())) return;
            fireServiceRevoked(bcssre);
            Iterator i;
            synchronized (children) {
                i = children.keySet().iterator();
            }
            while (i.hasNext()) {
                Object c = i.next();
                if (c instanceof BeanContextServices) {
                    ((BeanContextServicesListener)(BeanContextServicesListener)c).serviceRevoked(bcssre);
                }
            }
        }
    }
    
    protected static final BeanContextServicesListener getChildBeanContextServicesListener(Object child) {
        try {
            return (BeanContextServicesListener)(BeanContextServicesListener)child;
        } catch (ClassCastException cce) {
            return null;
        }
    }
    
    protected void childJustRemovedHook(Object child, BeanContextSupport$BCSChild bcsc) {
        BeanContextServicesSupport$BCSSChild bcssc = (BeanContextServicesSupport$BCSSChild)(BeanContextServicesSupport$BCSSChild)bcsc;
        bcssc.cleanupReferences();
    }
    
    protected synchronized void releaseBeanContextResources() {
        Object[] bcssc;
        super.releaseBeanContextResources();
        synchronized (children) {
            if (children.isEmpty()) return;
            bcssc = children.values().toArray();
        }
        for (int i = 0; i < bcssc.length; i++) {
            ((BeanContextServicesSupport$BCSSChild)(BeanContextServicesSupport$BCSSChild)bcssc[i]).revokeAllDelegatedServicesNow();
        }
        proxy = null;
    }
    
    protected synchronized void initializeBeanContextResources() {
        super.initializeBeanContextResources();
        BeanContext nbc = getBeanContext();
        if (nbc == null) return;
        try {
            BeanContextServices bcs = (BeanContextServices)(BeanContextServices)nbc;
            proxy = new BeanContextServicesSupport$BCSSProxyServiceProvider(this, bcs);
        } catch (ClassCastException cce) {
        }
    }
    
    protected final void fireServiceAdded(Class serviceClass) {
        BeanContextServiceAvailableEvent bcssae = new BeanContextServiceAvailableEvent(getBeanContextServicesPeer(), serviceClass);
        fireServiceAdded(bcssae);
    }
    
    protected final void fireServiceAdded(BeanContextServiceAvailableEvent bcssae) {
        Object[] copy;
        synchronized (bcsListeners) {
            copy = bcsListeners.toArray();
        }
        for (int i = 0; i < copy.length; i++) {
            ((BeanContextServicesListener)(BeanContextServicesListener)copy[i]).serviceAvailable(bcssae);
        }
    }
    
    protected final void fireServiceRevoked(BeanContextServiceRevokedEvent bcsre) {
        Object[] copy;
        synchronized (bcsListeners) {
            copy = bcsListeners.toArray();
        }
        for (int i = 0; i < copy.length; i++) {
            ((BeanContextServiceRevokedListener)(BeanContextServiceRevokedListener)copy[i]).serviceRevoked(bcsre);
        }
    }
    
    protected final void fireServiceRevoked(Class serviceClass, boolean revokeNow) {
        Object[] copy;
        BeanContextServiceRevokedEvent bcsre = new BeanContextServiceRevokedEvent(getBeanContextServicesPeer(), serviceClass, revokeNow);
        synchronized (bcsListeners) {
            copy = bcsListeners.toArray();
        }
        for (int i = 0; i < copy.length; i++) {
            ((BeanContextServicesListener)(BeanContextServicesListener)copy[i]).serviceRevoked(bcsre);
        }
    }
    
    protected synchronized void bcsPreSerializationHook(ObjectOutputStream oos) throws IOException {
        oos.writeInt(serializable);
        if (serializable <= 0) return;
        int count = 0;
        Iterator i = services.entrySet().iterator();
        while (i.hasNext() && count < serializable) {
            Map$Entry entry = (Map$Entry)(Map$Entry)i.next();
            BeanContextServicesSupport$BCSSServiceProvider bcsp = null;
            try {
                bcsp = (BeanContextServicesSupport$BCSSServiceProvider)(BeanContextServicesSupport$BCSSServiceProvider)entry.getValue();
            } catch (ClassCastException cce) {
                continue;
            }
            if (bcsp.getServiceProvider() instanceof Serializable) {
                oos.writeObject(entry.getKey());
                oos.writeObject(bcsp);
                count++;
            }
        }
        if (count != serializable) throw new IOException("wrote different number of service providers than expected");
    }
    
    protected synchronized void bcsPreDeserializationHook(ObjectInputStream ois) throws IOException, ClassNotFoundException {
        serializable = ois.readInt();
        int count = serializable;
        while (count > 0) {
            services.put(ois.readObject(), ois.readObject());
            count--;
        }
    }
    
    private synchronized void writeObject(ObjectOutputStream oos) throws IOException {
        oos.defaultWriteObject();
        serialize(oos, (Collection)bcsListeners);
    }
    
    private synchronized void readObject(ObjectInputStream ois) throws IOException, ClassNotFoundException {
        ois.defaultReadObject();
        deserialize(ois, (Collection)bcsListeners);
    }
    protected transient HashMap services;
    protected transient int serializable = 0;
    protected transient BeanContextServicesSupport$BCSSProxyServiceProvider proxy;
    protected transient ArrayList bcsListeners;
}
