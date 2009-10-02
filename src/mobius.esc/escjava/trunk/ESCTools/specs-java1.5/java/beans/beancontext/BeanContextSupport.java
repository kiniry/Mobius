package java.beans.beancontext;

import java.awt.Component;
import java.awt.Container;
import java.beans.Beans;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.VetoableChangeListener;
import java.beans.PropertyVetoException;
import java.beans.Visibility;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Locale;

public class BeanContextSupport extends BeanContextChildSupport implements BeanContext, Serializable, PropertyChangeListener, VetoableChangeListener {
    static final long serialVersionUID = -4879613978649577204L;
    
    public BeanContextSupport(BeanContext peer, Locale lcle, boolean dTime, boolean visible) {
        super(peer);
        locale = lcle != null ? lcle : Locale.getDefault();
        designTime = dTime;
        okToUseGui = visible;
        initialize();
    }
    
    public BeanContextSupport(BeanContext peer, Locale lcle, boolean dtime) {
        this(peer, lcle, dtime, true);
    }
    
    public BeanContextSupport(BeanContext peer, Locale lcle) {
        this(peer, lcle, false, true);
    }
    
    public BeanContextSupport(BeanContext peer) {
        this(peer, null, false, true);
    }
    
    public BeanContextSupport() {
        this(null, null, false, true);
    }
    
    public BeanContext getBeanContextPeer() {
        return (BeanContext)(BeanContext)getBeanContextChildPeer();
    }
    
    public Object instantiateChild(String beanName) throws IOException, ClassNotFoundException {
        BeanContext bc = getBeanContextPeer();
        return Beans.instantiate(bc.getClass().getClassLoader(), beanName, bc);
    }
    
    public int size() {
        synchronized (children) {
            return children.size();
        }
    }
    
    public boolean isEmpty() {
        synchronized (children) {
            return children.isEmpty();
        }
    }
    
    public boolean contains(Object o) {
        synchronized (children) {
            return children.containsKey(o);
        }
    }
    
    public boolean containsKey(Object o) {
        synchronized (children) {
            return children.containsKey(o);
        }
    }
    
    public Iterator iterator() {
        synchronized (children) {
            return new BeanContextSupport$BCSIterator(children.keySet().iterator());
        }
    }
    
    public Object[] toArray() {
        synchronized (children) {
            return children.keySet().toArray();
        }
    }
    
    public Object[] toArray(Object[] arry) {
        synchronized (children) {
            return children.keySet().toArray(arry);
        }
    }
    {
    }
    {
    }
    
    protected BeanContextSupport$BCSChild createBCSChild(Object targetChild, Object peer) {
        return new BeanContextSupport$BCSChild(this, targetChild, peer);
    }
    
    public boolean add(Object targetChild) {
        if (targetChild == null) throw new IllegalArgumentException();
        if (children.containsKey(targetChild)) return false;
        synchronized (BeanContext.globalHierarchyLock) {
            if (children.containsKey(targetChild)) return false;
            if (!validatePendingAdd(targetChild)) {
                throw new IllegalStateException();
            }
            BeanContextChild cbcc = getChildBeanContextChild(targetChild);
            BeanContextChild bccp = null;
            synchronized (targetChild) {
                if (targetChild instanceof BeanContextProxy) {
                    bccp = ((BeanContextProxy)(BeanContextProxy)targetChild).getBeanContextProxy();
                    if (bccp == null) throw new NullPointerException("BeanContextPeer.getBeanContextProxy()");
                }
                BeanContextSupport$BCSChild bcsc = createBCSChild(targetChild, bccp);
                BeanContextSupport$BCSChild pbcsc = null;
                synchronized (children) {
                    children.put(targetChild, bcsc);
                    if (bccp != null) children.put(bccp, pbcsc = createBCSChild(bccp, targetChild));
                }
                if (cbcc != null) synchronized (cbcc) {
                    try {
                        cbcc.setBeanContext(getBeanContextPeer());
                    } catch (PropertyVetoException pve) {
                        synchronized (children) {
                            children.remove(targetChild);
                            if (bccp != null) children.remove(bccp);
                        }
                        throw new IllegalStateException();
                    }
                    cbcc.addPropertyChangeListener("beanContext", childPCL);
                    cbcc.addVetoableChangeListener("beanContext", childVCL);
                }
                Visibility v = getChildVisibility(targetChild);
                if (v != null) {
                    if (okToUseGui) v.okToUseGui(); else v.dontUseGui();
                }
                if (getChildSerializable(targetChild) != null) serializable++;
                childJustAddedHook(targetChild, bcsc);
                if (bccp != null) {
                    v = getChildVisibility(bccp);
                    if (v != null) {
                        if (okToUseGui) v.okToUseGui(); else v.dontUseGui();
                    }
                    if (getChildSerializable(bccp) != null) serializable++;
                    childJustAddedHook(bccp, pbcsc);
                }
            }
            fireChildrenAdded(new BeanContextMembershipEvent(getBeanContextPeer(), bccp == null ? new Object[]{targetChild} : new Object[]{targetChild, bccp}));
        }
        return true;
    }
    
    public boolean remove(Object targetChild) {
        return remove(targetChild, true);
    }
    
    protected boolean remove(Object targetChild, boolean callChildSetBC) {
        if (targetChild == null) throw new IllegalArgumentException();
        synchronized (BeanContext.globalHierarchyLock) {
            if (!containsKey(targetChild)) return false;
            if (!validatePendingRemove(targetChild)) {
                throw new IllegalStateException();
            }
            BeanContextSupport$BCSChild bcsc = (BeanContextSupport$BCSChild)(BeanContextSupport$BCSChild)children.get(targetChild);
            BeanContextSupport$BCSChild pbcsc = null;
            Object peer = null;
            synchronized (targetChild) {
                if (callChildSetBC) {
                    BeanContextChild cbcc = getChildBeanContextChild(targetChild);
                    if (cbcc != null) synchronized (cbcc) {
                        cbcc.removePropertyChangeListener("beanContext", childPCL);
                        cbcc.removeVetoableChangeListener("beanContext", childVCL);
                        try {
                            cbcc.setBeanContext(null);
                        } catch (PropertyVetoException pve1) {
                            cbcc.addPropertyChangeListener("beanContext", childPCL);
                            cbcc.addVetoableChangeListener("beanContext", childVCL);
                            throw new IllegalStateException();
                        }
                    }
                }
                synchronized (children) {
                    children.remove(targetChild);
                    if (bcsc.isProxyPeer()) {
                        pbcsc = (BeanContextSupport$BCSChild)(BeanContextSupport$BCSChild)children.get(peer = bcsc.getProxyPeer());
                        children.remove(peer);
                    }
                }
                if (getChildSerializable(targetChild) != null) serializable--;
                childJustRemovedHook(targetChild, bcsc);
                if (peer != null) {
                    if (getChildSerializable(peer) != null) serializable--;
                    childJustRemovedHook(peer, pbcsc);
                }
            }
            fireChildrenRemoved(new BeanContextMembershipEvent(getBeanContextPeer(), peer == null ? new Object[]{targetChild} : new Object[]{targetChild, peer}));
        }
        return true;
    }
    
    public boolean containsAll(Collection c) {
        synchronized (children) {
            Iterator i = c.iterator();
            while (i.hasNext()) if (!contains(i.next())) return false;
            return true;
        }
    }
    
    public boolean addAll(Collection c) {
        throw new UnsupportedOperationException();
    }
    
    public boolean removeAll(Collection c) {
        throw new UnsupportedOperationException();
    }
    
    public boolean retainAll(Collection c) {
        throw new UnsupportedOperationException();
    }
    
    public void clear() {
        throw new UnsupportedOperationException();
    }
    
    public void addBeanContextMembershipListener(BeanContextMembershipListener bcml) {
        if (bcml == null) throw new NullPointerException("listener");
        synchronized (bcmListeners) {
            if (bcmListeners.contains(bcml)) return; else bcmListeners.add(bcml);
        }
    }
    
    public void removeBeanContextMembershipListener(BeanContextMembershipListener bcml) {
        if (bcml == null) throw new NullPointerException("listener");
        synchronized (bcmListeners) {
            if (!bcmListeners.contains(bcml)) return; else bcmListeners.remove(bcml);
        }
    }
    
    public InputStream getResourceAsStream(String name, BeanContextChild bcc) {
        if (name == null) throw new NullPointerException("name");
        if (bcc == null) throw new NullPointerException("bcc");
        if (containsKey(bcc)) {
            ClassLoader cl = bcc.getClass().getClassLoader();
            return cl != null ? cl.getResourceAsStream(name) : ClassLoader.getSystemResourceAsStream(name);
        } else throw new IllegalArgumentException("Not a valid child");
    }
    
    public URL getResource(String name, BeanContextChild bcc) {
        if (name == null) throw new NullPointerException("name");
        if (bcc == null) throw new NullPointerException("bcc");
        if (containsKey(bcc)) {
            ClassLoader cl = bcc.getClass().getClassLoader();
            return cl != null ? cl.getResource(name) : ClassLoader.getSystemResource(name);
        } else throw new IllegalArgumentException("Not a valid child");
    }
    
    public synchronized void setDesignTime(boolean dTime) {
        if (designTime != dTime) {
            designTime = dTime;
            firePropertyChange("designMode", Boolean.valueOf(!dTime), Boolean.valueOf(dTime));
        }
    }
    
    public synchronized boolean isDesignTime() {
        return designTime;
    }
    
    public synchronized void setLocale(Locale newLocale) throws PropertyVetoException {
        if ((locale != null && !locale.equals(newLocale)) && newLocale != null) {
            Locale old = locale;
            fireVetoableChange("locale", old, newLocale);
            locale = newLocale;
            firePropertyChange("locale", old, newLocale);
        }
    }
    
    public synchronized Locale getLocale() {
        return locale;
    }
    
    public synchronized boolean needsGui() {
        BeanContext bc = getBeanContextPeer();
        if (bc != this) {
            if (bc instanceof Visibility) return ((Visibility)bc).needsGui();
            if (bc instanceof Container || bc instanceof Component) return true;
        }
        synchronized (children) {
            for (Iterator i = children.keySet().iterator(); i.hasNext(); ) {
                Object c = i.next();
                try {
                    return ((Visibility)(Visibility)c).needsGui();
                } catch (ClassCastException cce) {
                }
                if (c instanceof Container || c instanceof Component) return true;
            }
        }
        return false;
    }
    
    public synchronized void dontUseGui() {
        if (okToUseGui) {
            okToUseGui = false;
            synchronized (children) {
                for (Iterator i = children.keySet().iterator(); i.hasNext(); ) {
                    Visibility v = getChildVisibility(i.next());
                    if (v != null) v.dontUseGui();
                }
            }
        }
    }
    
    public synchronized void okToUseGui() {
        if (!okToUseGui) {
            okToUseGui = true;
            synchronized (children) {
                for (Iterator i = children.keySet().iterator(); i.hasNext(); ) {
                    Visibility v = getChildVisibility(i.next());
                    if (v != null) v.okToUseGui();
                }
            }
        }
    }
    
    public boolean avoidingGui() {
        return !okToUseGui && needsGui();
    }
    
    public boolean isSerializing() {
        return serializing;
    }
    
    protected Iterator bcsChildren() {
        synchronized (children) {
            return children.values().iterator();
        }
    }
    
    protected void bcsPreSerializationHook(ObjectOutputStream oos) throws IOException {
    }
    
    protected void bcsPreDeserializationHook(ObjectInputStream ois) throws IOException, ClassNotFoundException {
    }
    
    protected void childDeserializedHook(Object child, BeanContextSupport$BCSChild bcsc) {
        synchronized (children) {
            children.put(child, bcsc);
        }
    }
    
    protected final void serialize(ObjectOutputStream oos, Collection coll) throws IOException {
        int count = 0;
        Object[] objects = coll.toArray();
        for (int i = 0; i < objects.length; i++) {
            if (objects[i] instanceof Serializable) count++; else objects[i] = null;
        }
        oos.writeInt(count);
        for (int i = 0; count > 0; i++) {
            Object o = objects[i];
            if (o != null) {
                oos.writeObject(o);
                count--;
            }
        }
    }
    
    protected final void deserialize(ObjectInputStream ois, Collection coll) throws IOException, ClassNotFoundException {
        int count = 0;
        count = ois.readInt();
        while (count-- > 0) {
            coll.add(ois.readObject());
        }
    }
    
    public final void writeChildren(ObjectOutputStream oos) throws IOException {
        if (serializable <= 0) return;
        boolean prev = serializing;
        serializing = true;
        int count = 0;
        synchronized (children) {
            Iterator i = children.entrySet().iterator();
            while (i.hasNext() && count < serializable) {
                Map$Entry entry = (Map$Entry)(Map$Entry)i.next();
                if (entry.getKey() instanceof Serializable) {
                    try {
                        oos.writeObject(entry.getKey());
                        oos.writeObject(entry.getValue());
                    } catch (IOException ioe) {
                        serializing = prev;
                        throw ioe;
                    }
                    count++;
                }
            }
        }
        serializing = prev;
        if (count != serializable) {
            throw new IOException("wrote different number of children than expected");
        }
    }
    
    private synchronized void writeObject(ObjectOutputStream oos) throws IOException, ClassNotFoundException {
        serializing = true;
        synchronized (BeanContext.globalHierarchyLock) {
            try {
                oos.defaultWriteObject();
                bcsPreSerializationHook(oos);
                if (serializable > 0 && this.equals(getBeanContextPeer())) writeChildren(oos);
                serialize(oos, (Collection)bcmListeners);
            } finally {
                serializing = false;
            }
        }
    }
    
    public final void readChildren(ObjectInputStream ois) throws IOException, ClassNotFoundException {
        int count = serializable;
        while (count-- > 0) {
            Object child = null;
            BeanContextSupport$BCSChild bscc = null;
            try {
                child = ois.readObject();
                bscc = (BeanContextSupport$BCSChild)(BeanContextSupport$BCSChild)ois.readObject();
            } catch (IOException ioe) {
                continue;
            } catch (ClassNotFoundException cnfe) {
                continue;
            }
            synchronized (child) {
                BeanContextChild bcc = null;
                try {
                    bcc = (BeanContextChild)(BeanContextChild)child;
                } catch (ClassCastException cce) {
                }
                if (bcc != null) {
                    try {
                        bcc.setBeanContext(getBeanContextPeer());
                        bcc.addPropertyChangeListener("beanContext", childPCL);
                        bcc.addVetoableChangeListener("beanContext", childVCL);
                    } catch (PropertyVetoException pve) {
                        continue;
                    }
                }
                childDeserializedHook(child, bscc);
            }
        }
    }
    
    private synchronized void readObject(ObjectInputStream ois) throws IOException, ClassNotFoundException {
        synchronized (BeanContext.globalHierarchyLock) {
            ois.defaultReadObject();
            initialize();
            bcsPreDeserializationHook(ois);
            if (serializable > 0 && this.equals(getBeanContextPeer())) readChildren(ois);
            deserialize(ois, bcmListeners = new ArrayList(1));
        }
    }
    
    public void vetoableChange(PropertyChangeEvent pce) throws PropertyVetoException {
        String propertyName = pce.getPropertyName();
        Object source = pce.getSource();
        synchronized (children) {
            if ("beanContext".equals(propertyName) && containsKey(source) && !getBeanContextPeer().equals(pce.getNewValue())) {
                if (!validatePendingRemove(source)) {
                    throw new PropertyVetoException("current BeanContext vetoes setBeanContext()", pce);
                } else ((BeanContextSupport$BCSChild)(BeanContextSupport$BCSChild)children.get(source)).setRemovePending(true);
            }
        }
    }
    
    public void propertyChange(PropertyChangeEvent pce) {
        String propertyName = pce.getPropertyName();
        Object source = pce.getSource();
        synchronized (children) {
            if ("beanContext".equals(propertyName) && containsKey(source) && ((BeanContextSupport$BCSChild)(BeanContextSupport$BCSChild)children.get(source)).isRemovePending()) {
                BeanContext bc = getBeanContextPeer();
                if (bc.equals(pce.getOldValue()) && !bc.equals(pce.getNewValue())) {
                    remove(source, false);
                } else {
                    ((BeanContextSupport$BCSChild)(BeanContextSupport$BCSChild)children.get(source)).setRemovePending(false);
                }
            }
        }
    }
    
    protected boolean validatePendingAdd(Object targetChild) {
        return true;
    }
    
    protected boolean validatePendingRemove(Object targetChild) {
        return true;
    }
    
    protected void childJustAddedHook(Object child, BeanContextSupport$BCSChild bcsc) {
    }
    
    protected void childJustRemovedHook(Object child, BeanContextSupport$BCSChild bcsc) {
    }
    
    protected static final Visibility getChildVisibility(Object child) {
        try {
            return (Visibility)(Visibility)child;
        } catch (ClassCastException cce) {
            return null;
        }
    }
    
    protected static final Serializable getChildSerializable(Object child) {
        try {
            return (Serializable)(Serializable)child;
        } catch (ClassCastException cce) {
            return null;
        }
    }
    
    protected static final PropertyChangeListener getChildPropertyChangeListener(Object child) {
        try {
            return (PropertyChangeListener)(PropertyChangeListener)child;
        } catch (ClassCastException cce) {
            return null;
        }
    }
    
    protected static final VetoableChangeListener getChildVetoableChangeListener(Object child) {
        try {
            return (VetoableChangeListener)(VetoableChangeListener)child;
        } catch (ClassCastException cce) {
            return null;
        }
    }
    
    protected static final BeanContextMembershipListener getChildBeanContextMembershipListener(Object child) {
        try {
            return (BeanContextMembershipListener)(BeanContextMembershipListener)child;
        } catch (ClassCastException cce) {
            return null;
        }
    }
    
    protected static final BeanContextChild getChildBeanContextChild(Object child) {
        try {
            BeanContextChild bcc = (BeanContextChild)(BeanContextChild)child;
            if (child instanceof BeanContextChild && child instanceof BeanContextProxy) throw new IllegalArgumentException("child cannot implement both BeanContextChild and BeanContextProxy"); else return bcc;
        } catch (ClassCastException cce) {
            try {
                return ((BeanContextProxy)(BeanContextProxy)child).getBeanContextProxy();
            } catch (ClassCastException cce1) {
                return null;
            }
        }
    }
    
    protected final void fireChildrenAdded(BeanContextMembershipEvent bcme) {
        Object[] copy;
        synchronized (bcmListeners) {
            copy = bcmListeners.toArray();
        }
        for (int i = 0; i < copy.length; i++) ((BeanContextMembershipListener)(BeanContextMembershipListener)copy[i]).childrenAdded(bcme);
    }
    
    protected final void fireChildrenRemoved(BeanContextMembershipEvent bcme) {
        Object[] copy;
        synchronized (bcmListeners) {
            copy = bcmListeners.toArray();
        }
        for (int i = 0; i < copy.length; i++) ((BeanContextMembershipListener)(BeanContextMembershipListener)copy[i]).childrenRemoved(bcme);
    }
    
    protected synchronized void initialize() {
        children = new HashMap(serializable + 1);
        bcmListeners = new ArrayList(1);
        childPCL = new BeanContextSupport$1(this);
        childVCL = new BeanContextSupport$2(this);
    }
    
    protected final Object[] copyChildren() {
        synchronized (children) {
            return children.keySet().toArray();
        }
    }
    
    protected static final boolean classEquals(Class first, Class second) {
        return first.equals(second) || first.getName().equals(second.getName());
    }
    protected transient HashMap children;
    private int serializable = 0;
    protected transient ArrayList bcmListeners;
    protected Locale locale;
    protected boolean okToUseGui;
    protected boolean designTime;
    private transient PropertyChangeListener childPCL;
    private transient VetoableChangeListener childVCL;
    private transient boolean serializing;
}
