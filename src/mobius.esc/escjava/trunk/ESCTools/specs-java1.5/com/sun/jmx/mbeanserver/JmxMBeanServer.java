package com.sun.jmx.mbeanserver;

import java.util.Iterator;
import java.util.Set;
import java.io.ObjectInputStream;
import java.security.AccessController;
import java.security.Permission;
import javax.management.MBeanPermission;
import javax.management.AttributeNotFoundException;
import javax.management.MBeanException;
import javax.management.ReflectionException;
import javax.management.MBeanInfo;
import javax.management.QueryExp;
import javax.management.NotificationListener;
import javax.management.NotificationFilter;
import javax.management.ListenerNotFoundException;
import javax.management.IntrospectionException;
import javax.management.OperationsException;
import javax.management.InstanceNotFoundException;
import javax.management.NotCompliantMBeanException;
import javax.management.MBeanRegistrationException;
import javax.management.InstanceAlreadyExistsException;
import javax.management.InvalidAttributeValueException;
import javax.management.ObjectName;
import javax.management.ObjectInstance;
import javax.management.Attribute;
import javax.management.AttributeList;
import javax.management.RuntimeOperationsException;
import javax.management.MBeanServer;
import javax.management.MBeanServerDelegate;
import javax.management.loading.ClassLoaderRepository;
import com.sun.jmx.interceptor.DefaultMBeanServerInterceptor;
import com.sun.jmx.interceptor.MBeanServerInterceptor;
import com.sun.jmx.defaults.ServiceName;
import com.sun.jmx.trace.Trace;

public final class JmxMBeanServer implements SunJmxMBeanServer {
    
    /*synthetic*/ static MBeanServerInterceptor access$200(JmxMBeanServer x0) {
        return x0.mbsInterceptor;
    }
    
    /*synthetic*/ static ObjectName access$100(JmxMBeanServer x0) {
        return x0.mBeanServerDelegateObjectName;
    }
    
    /*synthetic*/ static MBeanServerDelegate access$000(JmxMBeanServer x0) {
        return x0.mBeanServerDelegateObject;
    }
    private static final String dbgTag = "MBeanServer";
    private final MBeanInstantiator instantiator;
    private final SecureClassLoaderRepository secureClr;
    private final MetaData meta;
    private final boolean interceptorsEnabled;
    private final transient MBeanServer outerShell;
    private transient MBeanServerInterceptor mbsInterceptor = null;
    private final transient MBeanServerDelegate mBeanServerDelegateObject;
    private transient ObjectName mBeanServerDelegateObjectName = null;
    
    JmxMBeanServer(String domain, MBeanServer outer, MBeanServerDelegate delegate) {
        this(domain, outer, delegate, null, null, false);
    }
    
    JmxMBeanServer(String domain, MBeanServer outer, MBeanServerDelegate delegate, boolean interceptors) {
        this(domain, outer, delegate, null, null, false);
    }
    
    JmxMBeanServer(String domain, MBeanServer outer, MBeanServerDelegate delegate, MBeanInstantiator instantiator, MetaData metadata, boolean interceptors) {
        
        if (instantiator == null) {
            final ModifiableClassLoaderRepository clr = new ClassLoaderRepositorySupport();
            instantiator = new MBeanInstantiatorImpl(clr);
        }
        this.secureClr = new SecureClassLoaderRepository(instantiator.getClassLoaderRepository());
        if (metadata == null) metadata = new MetaDataImpl(instantiator);
        if (delegate == null) delegate = new MBeanServerDelegateImpl();
        if (outer == null) outer = this;
        this.instantiator = instantiator;
        this.meta = metadata;
        this.mBeanServerDelegateObject = delegate;
        this.outerShell = outer;
        final Repository repository = new RepositorySupport(domain);
        this.mbsInterceptor = new DefaultMBeanServerInterceptor(outer, delegate, instantiator, metadata, repository);
        this.interceptorsEnabled = interceptors;
        initialize();
    }
    
    public boolean interceptorsEnabled() {
        return interceptorsEnabled;
    }
    
    public MBeanInstantiator getMBeanInstantiator() {
        if (interceptorsEnabled) return instantiator; else throw new UnsupportedOperationException("MBeanServerInterceptors are disabled.");
    }
    
    public MetaData getMetaData() {
        return meta;
    }
    
    public ObjectInstance createMBean(String className, ObjectName name) throws ReflectionException, InstanceAlreadyExistsException, MBeanRegistrationException, MBeanException, NotCompliantMBeanException {
        return mbsInterceptor.createMBean(className, cloneObjectName(name), (Object[])null, (String[])null);
    }
    
    public ObjectInstance createMBean(String className, ObjectName name, ObjectName loaderName) throws ReflectionException, InstanceAlreadyExistsException, MBeanRegistrationException, MBeanException, NotCompliantMBeanException, InstanceNotFoundException {
        return mbsInterceptor.createMBean(className, cloneObjectName(name), loaderName, (Object[])null, (String[])null);
    }
    
    public ObjectInstance createMBean(String className, ObjectName name, Object[] params, String[] signature) throws ReflectionException, InstanceAlreadyExistsException, MBeanRegistrationException, MBeanException, NotCompliantMBeanException {
        return mbsInterceptor.createMBean(className, cloneObjectName(name), params, signature);
    }
    
    public ObjectInstance createMBean(String className, ObjectName name, ObjectName loaderName, Object[] params, String[] signature) throws ReflectionException, InstanceAlreadyExistsException, MBeanRegistrationException, MBeanException, NotCompliantMBeanException, InstanceNotFoundException {
        return mbsInterceptor.createMBean(className, cloneObjectName(name), loaderName, params, signature);
    }
    
    public ObjectInstance registerMBean(Object object, ObjectName name) throws InstanceAlreadyExistsException, MBeanRegistrationException, NotCompliantMBeanException {
        return mbsInterceptor.registerMBean(object, cloneObjectName(name));
    }
    
    public void unregisterMBean(ObjectName name) throws InstanceNotFoundException, MBeanRegistrationException {
        mbsInterceptor.unregisterMBean(cloneObjectName(name));
    }
    
    public ObjectInstance getObjectInstance(ObjectName name) throws InstanceNotFoundException {
        return mbsInterceptor.getObjectInstance(cloneObjectName(name));
    }
    
    public Set queryMBeans(ObjectName name, QueryExp query) {
        return mbsInterceptor.queryMBeans(cloneObjectName(name), query);
    }
    
    public Set queryNames(ObjectName name, QueryExp query) {
        return mbsInterceptor.queryNames(cloneObjectName(name), query);
    }
    
    public boolean isRegistered(ObjectName name) {
        return mbsInterceptor.isRegistered(name);
    }
    
    public Integer getMBeanCount() {
        return mbsInterceptor.getMBeanCount();
    }
    
    public Object getAttribute(ObjectName name, String attribute) throws MBeanException, AttributeNotFoundException, InstanceNotFoundException, ReflectionException {
        return mbsInterceptor.getAttribute(cloneObjectName(name), attribute);
    }
    
    public AttributeList getAttributes(ObjectName name, String[] attributes) throws InstanceNotFoundException, ReflectionException {
        return mbsInterceptor.getAttributes(cloneObjectName(name), attributes);
    }
    
    public void setAttribute(ObjectName name, Attribute attribute) throws InstanceNotFoundException, AttributeNotFoundException, InvalidAttributeValueException, MBeanException, ReflectionException {
        mbsInterceptor.setAttribute(cloneObjectName(name), cloneAttribute(attribute));
    }
    
    public AttributeList setAttributes(ObjectName name, AttributeList attributes) throws InstanceNotFoundException, ReflectionException {
        return mbsInterceptor.setAttributes(cloneObjectName(name), cloneAttributeList(attributes));
    }
    
    public Object invoke(ObjectName name, String operationName, Object[] params, String[] signature) throws InstanceNotFoundException, MBeanException, ReflectionException {
        return mbsInterceptor.invoke(cloneObjectName(name), operationName, params, signature);
    }
    
    public String getDefaultDomain() {
        return mbsInterceptor.getDefaultDomain();
    }
    
    public String[] getDomains() {
        return mbsInterceptor.getDomains();
    }
    
    public void addNotificationListener(ObjectName name, NotificationListener listener, NotificationFilter filter, Object handback) throws InstanceNotFoundException {
        mbsInterceptor.addNotificationListener(cloneObjectName(name), listener, filter, handback);
    }
    
    public void addNotificationListener(ObjectName name, ObjectName listener, NotificationFilter filter, Object handback) throws InstanceNotFoundException {
        mbsInterceptor.addNotificationListener(cloneObjectName(name), listener, filter, handback);
    }
    
    public void removeNotificationListener(ObjectName name, NotificationListener listener) throws InstanceNotFoundException, ListenerNotFoundException {
        mbsInterceptor.removeNotificationListener(cloneObjectName(name), listener);
    }
    
    public void removeNotificationListener(ObjectName name, NotificationListener listener, NotificationFilter filter, Object handback) throws InstanceNotFoundException, ListenerNotFoundException {
        mbsInterceptor.removeNotificationListener(cloneObjectName(name), listener, filter, handback);
    }
    
    public void removeNotificationListener(ObjectName name, ObjectName listener) throws InstanceNotFoundException, ListenerNotFoundException {
        mbsInterceptor.removeNotificationListener(cloneObjectName(name), listener);
    }
    
    public void removeNotificationListener(ObjectName name, ObjectName listener, NotificationFilter filter, Object handback) throws InstanceNotFoundException, ListenerNotFoundException {
        mbsInterceptor.removeNotificationListener(cloneObjectName(name), listener, filter, handback);
    }
    
    public MBeanInfo getMBeanInfo(ObjectName name) throws InstanceNotFoundException, IntrospectionException, ReflectionException {
        return mbsInterceptor.getMBeanInfo(cloneObjectName(name));
    }
    
    public Object instantiate(String className) throws ReflectionException, MBeanException {
        checkMBeanPermission(className, null, null, "instantiate");
        return instantiator.instantiate(className);
    }
    
    public Object instantiate(String className, ObjectName loaderName) throws ReflectionException, MBeanException, InstanceNotFoundException {
        checkMBeanPermission(className, null, null, "instantiate");
        ClassLoader myLoader = outerShell.getClass().getClassLoader();
        return instantiator.instantiate(className, loaderName, myLoader);
    }
    
    public Object instantiate(String className, Object[] params, String[] signature) throws ReflectionException, MBeanException {
        checkMBeanPermission(className, null, null, "instantiate");
        ClassLoader myLoader = outerShell.getClass().getClassLoader();
        return instantiator.instantiate(className, params, signature, myLoader);
    }
    
    public Object instantiate(String className, ObjectName loaderName, Object[] params, String[] signature) throws ReflectionException, MBeanException, InstanceNotFoundException {
        checkMBeanPermission(className, null, null, "instantiate");
        ClassLoader myLoader = outerShell.getClass().getClassLoader();
        return instantiator.instantiate(className, loaderName, params, signature, myLoader);
    }
    
    public boolean isInstanceOf(ObjectName name, String className) throws InstanceNotFoundException {
        return mbsInterceptor.isInstanceOf(cloneObjectName(name), className);
    }
    
    public ObjectInputStream deserialize(ObjectName name, byte[] data) throws InstanceNotFoundException, OperationsException {
        final ClassLoader loader = getClassLoaderFor(name);
        return instantiator.deserialize(loader, data);
    }
    
    public ObjectInputStream deserialize(String className, byte[] data) throws OperationsException, ReflectionException {
        if (className == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException(), "Null className passed in parameter");
        }
        final ClassLoaderRepository clr = getClassLoaderRepository();
        Class theClass;
        try {
            if (clr == null) throw new ClassNotFoundException(className);
            theClass = clr.loadClass(className);
        } catch (ClassNotFoundException e) {
            throw new ReflectionException(e, "The given class could not be loaded by the default loader repository");
        }
        return instantiator.deserialize(theClass.getClassLoader(), data);
    }
    
    public ObjectInputStream deserialize(String className, ObjectName loaderName, byte[] data) throws InstanceNotFoundException, OperationsException, ReflectionException {
        loaderName = cloneObjectName(loaderName);
        try {
            getClassLoader(loaderName);
        } catch (SecurityException e) {
            throw e;
        } catch (Exception e) {
        }
        ClassLoader myLoader = outerShell.getClass().getClassLoader();
        return instantiator.deserialize(className, loaderName, data, myLoader);
    }
    
    private void initialize() {
        if (instantiator == null) throw new IllegalStateException("instantiator must not be null.");
        try {
            mBeanServerDelegateObjectName = new ObjectName(ServiceName.DELEGATE);
            AccessController.doPrivileged(new JmxMBeanServer$1(this));
        } catch (SecurityException e) {
            if (isDebugOn()) {
                debug("new", "Unexpected security exception occured: " + e);
            }
            mBeanServerDelegateObjectName = null;
            throw e;
        } catch (Exception e) {
            if (isDebugOn()) {
                debug("new", "Unexpected exception occured: " + e.getClass().getName());
            }
            mBeanServerDelegateObjectName = null;
            throw new IllegalStateException("Can\'t register delegate.");
        }
        ClassLoader myLoader = outerShell.getClass().getClassLoader();
        final ModifiableClassLoaderRepository loaders = instantiator.getClassLoaderRepository();
        if (loaders != null) {
            loaders.addClassLoader(myLoader);
            ClassLoader systemLoader = ClassLoader.getSystemClassLoader();
            if (systemLoader != myLoader) loaders.addClassLoader(systemLoader);
        }
    }
    
    public synchronized MBeanServerInterceptor getMBeanServerInterceptor() {
        if (interceptorsEnabled) return mbsInterceptor; else throw new UnsupportedOperationException("MBeanServerInterceptors are disabled.");
    }
    
    public synchronized void setMBeanServerInterceptor(MBeanServerInterceptor interceptor) {
        if (!interceptorsEnabled) throw new UnsupportedOperationException("MBeanServerInterceptors are disabled.");
        if (interceptor == null) throw new IllegalArgumentException("MBeanServerInterceptor is null");
        mbsInterceptor = interceptor;
    }
    
    public ClassLoader getClassLoaderFor(ObjectName mbeanName) throws InstanceNotFoundException {
        return mbsInterceptor.getClassLoaderFor(cloneObjectName(mbeanName));
    }
    
    public ClassLoader getClassLoader(ObjectName loaderName) throws InstanceNotFoundException {
        return mbsInterceptor.getClassLoader(cloneObjectName(loaderName));
    }
    
    public ClassLoaderRepository getClassLoaderRepository() {
        checkMBeanPermission(null, null, null, "getClassLoaderRepository");
        return secureClr;
    }
    
    public MBeanServerDelegate getMBeanServerDelegate() {
        return mBeanServerDelegateObject;
    }
    
    public static MBeanServerDelegate newMBeanServerDelegate() {
        return new MBeanServerDelegateImpl();
    }
    
    public static MBeanServer newMBeanServer(String defaultDomain, MBeanServer outer, MBeanServerDelegate delegate, boolean interceptors) {
        return new JmxMBeanServer(defaultDomain, outer, delegate, interceptors);
    }
    
    private ObjectName cloneObjectName(ObjectName name) {
        if (name != null) {
            return ObjectName.getInstance(name);
        }
        return name;
    }
    
    private Attribute cloneAttribute(Attribute attribute) {
        if (attribute != null) {
            if (!attribute.getClass().equals(Attribute.class)) {
                return new Attribute(attribute.getName(), attribute.getValue());
            }
        }
        return attribute;
    }
    
    private AttributeList cloneAttributeList(AttributeList list) {
        if (list != null) {
            if (!list.getClass().equals(AttributeList.class)) {
                AttributeList newList = new AttributeList(list.size());
                for (Iterator i = list.iterator(); i.hasNext(); ) {
                    Attribute attribute = (Attribute)(Attribute)i.next();
                    newList.add(cloneAttribute(attribute));
                }
                return newList;
            } else {
                for (int i = 0; i < list.size(); i++) {
                    Attribute attribute = (Attribute)(Attribute)list.get(i);
                    if (!attribute.getClass().equals(Attribute.class)) {
                        list.set(i, cloneAttribute(attribute));
                    }
                }
                return list;
            }
        }
        return list;
    }
    
    private static void checkMBeanPermission(String classname, String member, ObjectName objectName, String actions) throws SecurityException {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            Permission perm = new MBeanPermission(classname, member, objectName, actions);
            sm.checkPermission(perm);
        }
    }
    
    private boolean isTraceOn() {
        return Trace.isSelected(Trace.LEVEL_TRACE, Trace.INFO_MBEANSERVER);
    }
    
    private void trace(String clz, String func, String info) {
        Trace.send(Trace.LEVEL_TRACE, Trace.INFO_MBEANSERVER, clz, func, info);
    }
    
    private void trace(String func, String info) {
        trace(dbgTag, func, info);
    }
    
    private boolean isDebugOn() {
        return Trace.isSelected(Trace.LEVEL_DEBUG, Trace.INFO_MBEANSERVER);
    }
    
    private void debug(String clz, String func, String info) {
        Trace.send(Trace.LEVEL_DEBUG, Trace.INFO_MBEANSERVER, clz, func, info);
    }
    
    private void debug(String func, String info) {
        debug(dbgTag, func, info);
    }
}
