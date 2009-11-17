package com.sun.jmx.interceptor;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Set;
import java.util.HashSet;
import java.util.WeakHashMap;
import java.lang.ref.WeakReference;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.security.AccessControlContext;
import java.security.Permission;
import java.security.ProtectionDomain;
import java.security.AccessController;
import javax.management.*;
import com.sun.jmx.mbeanserver.ModifiableClassLoaderRepository;
import com.sun.jmx.mbeanserver.MetaData;
import com.sun.jmx.mbeanserver.MetaDataImpl;
import com.sun.jmx.mbeanserver.MBeanInstantiator;
import com.sun.jmx.mbeanserver.Repository;
import com.sun.jmx.mbeanserver.RepositorySupport;
import com.sun.jmx.mbeanserver.NamedObject;
import com.sun.jmx.defaults.ServiceName;
import com.sun.jmx.trace.Trace;

public class DefaultMBeanServerInterceptor implements MBeanServerInterceptor {
    private static final ObjectName _MBSDelegateObjectName;
    static {
        try {
            _MBSDelegateObjectName = new ObjectName(ServiceName.DELEGATE);
        } catch (MalformedObjectNameException e) {
            throw new UnsupportedOperationException(e.getMessage());
        }
    }
    private final transient MBeanInstantiator instantiator;
    private transient MBeanServer server = null;
    private final transient MBeanServerDelegate delegate;
    private final transient MetaData meta;
    private final transient Repository repository;
    private final transient WeakHashMap listenerWrappers = new WeakHashMap();
    private final String domain;
    private boolean queryByRepo;
    private static final String dbgTag = "DefaultMBeanServerInterceptor";
    
    public DefaultMBeanServerInterceptor(String domain, MBeanServer outer, MBeanServerDelegate delegate, MBeanInstantiator instantiator) {
        this(outer, delegate, instantiator, null, new RepositorySupport((domain == null ? ServiceName.DOMAIN : domain)));
    }
    
    public DefaultMBeanServerInterceptor(MBeanServer outer, MBeanServerDelegate delegate, MBeanInstantiator instantiator, MetaData metadata, Repository repository) {
        
        if (outer == null) throw new IllegalArgumentException("outer MBeanServer cannot be null");
        if (delegate == null) throw new IllegalArgumentException("MBeanServerDelegate cannot be null");
        if (instantiator == null) throw new IllegalArgumentException("MBeanInstantiator cannot be null");
        if (metadata == null) metadata = new MetaDataImpl(instantiator);
        if (repository == null) repository = new RepositorySupport(ServiceName.DOMAIN);
        this.server = outer;
        this.delegate = delegate;
        this.instantiator = instantiator;
        this.meta = metadata;
        this.repository = repository;
        this.domain = repository.getDefaultDomain();
    }
    
    public ObjectInstance createMBean(String className, ObjectName name) throws ReflectionException, InstanceAlreadyExistsException, MBeanRegistrationException, MBeanException, NotCompliantMBeanException {
        return createMBean(className, name, (Object[])null, (String[])null);
    }
    
    public ObjectInstance createMBean(String className, ObjectName name, ObjectName loaderName) throws ReflectionException, InstanceAlreadyExistsException, MBeanRegistrationException, MBeanException, NotCompliantMBeanException, InstanceNotFoundException {
        return createMBean(className, name, loaderName, (Object[])null, (String[])null);
    }
    
    public ObjectInstance createMBean(String className, ObjectName name, Object[] params, String[] signature) throws ReflectionException, InstanceAlreadyExistsException, MBeanRegistrationException, MBeanException, NotCompliantMBeanException {
        try {
            return createMBean(className, name, null, true, params, signature);
        } catch (InstanceNotFoundException e) {
            throw new IllegalArgumentException("Unexpected exception: " + e);
        }
    }
    
    public ObjectInstance createMBean(String className, ObjectName name, ObjectName loaderName, Object[] params, String[] signature) throws ReflectionException, InstanceAlreadyExistsException, MBeanRegistrationException, MBeanException, NotCompliantMBeanException, InstanceNotFoundException {
        return createMBean(className, name, loaderName, false, params, signature);
    }
    
    private ObjectInstance createMBean(String className, ObjectName name, ObjectName loaderName, boolean withDefaultLoaderRepository, Object[] params, String[] signature) throws ReflectionException, InstanceAlreadyExistsException, MBeanRegistrationException, MBeanException, NotCompliantMBeanException, InstanceNotFoundException {
        ObjectName logicalName = name;
        Class theClass;
        if (className == null) {
            final RuntimeException wrapped = new IllegalArgumentException("The class name cannot be null");
            throw new RuntimeOperationsException(wrapped, "Exception occured during MBean creation");
        }
        if (name != null) {
            if (name.isPattern()) {
                final RuntimeException wrapped = new IllegalArgumentException("Invalid name->" + name.toString());
                final String msg = "Exception occurred during MBean creation";
                throw new RuntimeOperationsException(wrapped, msg);
            }
            name = nonDefaultDomain(name);
        }
        checkMBeanPermission(className, null, null, "instantiate");
        checkMBeanPermission(className, null, name, "registerMBean");
        if (withDefaultLoaderRepository) {
            if (isTraceOn()) {
                trace(dbgTag, "createMBean", "ClassName = " + className + ",ObjectName = " + name);
            }
            theClass = instantiator.findClassWithDefaultLoaderRepository(className);
        } else if (loaderName == null) {
            if (isTraceOn()) {
                trace(dbgTag, "createMBean", "ClassName = " + className + ",ObjectName = " + name + " Loader name = null");
            }
            theClass = instantiator.findClass(className, server.getClass().getClassLoader());
        } else {
            loaderName = nonDefaultDomain(loaderName);
            if (isTraceOn()) {
                trace(dbgTag, "createMBean", "ClassName = " + className + ",ObjectName = " + name + ",Loader name = " + loaderName.toString());
            }
            theClass = instantiator.findClass(className, loaderName);
        }
        checkMBeanTrustPermission(theClass);
        instantiator.testCreation(theClass);
        meta.testCompliance(theClass);
        Object moi = instantiator.instantiate(theClass, params, signature, server.getClass().getClassLoader());
        final String infoClassName;
        try {
            infoClassName = meta.getMBeanClassName(moi);
        } catch (IntrospectionException e) {
            throw new NotCompliantMBeanException(e.getMessage());
        }
        return registerCreatedObject(infoClassName, moi, name);
    }
    
    public ObjectInstance registerMBean(Object object, ObjectName name) throws InstanceAlreadyExistsException, MBeanRegistrationException, NotCompliantMBeanException {
        Class theClass = object.getClass();
        meta.testCompliance(theClass);
        final String infoClassName;
        try {
            infoClassName = meta.getMBeanClassName(object);
        } catch (IntrospectionException e) {
            throw new NotCompliantMBeanException(e.getMessage());
        }
        checkMBeanPermission(infoClassName, null, name, "registerMBean");
        checkMBeanTrustPermission(theClass);
        return registerObject(infoClassName, object, name);
    }
    
    public void unregisterMBean(ObjectName name) throws InstanceNotFoundException, MBeanRegistrationException {
        Object object;
        if (name == null) {
            final RuntimeException wrapped = new IllegalArgumentException("Object name cannot be null");
            throw new RuntimeOperationsException(wrapped, "Exception occured trying to unregister the MBean");
        }
        name = nonDefaultDomain(name);
        Object instance = getMBean(name);
        String classname = null;
        try {
            classname = meta.getMBeanClassName(instance);
        } catch (IntrospectionException e) {
            classname = null;
        } catch (NotCompliantMBeanException e) {
            classname = null;
        }
        checkMBeanPermission(classname, null, name, "unregisterMBean");
        synchronized (this) {
            object = repository.retrieve(name);
            if (object == null) {
                if (isTraceOn()) {
                    trace("unregisterMBean", name + ": Found no object");
                }
                throw new InstanceNotFoundException(name.toString());
            }
            if (object instanceof MBeanRegistration) {
                meta.preDeregisterInvoker(object);
            }
            try {
                repository.remove(name);
            } catch (InstanceNotFoundException e) {
                throw e;
            }
            if (object instanceof ClassLoader && object != server.getClass().getClassLoader()) {
                final ModifiableClassLoaderRepository clr = instantiator.getClassLoaderRepository();
                if (clr != null) clr.removeClassLoader(name);
            }
        }
        if (isTraceOn()) {
            trace("unregisterMBean", "Send delete notification of object " + name.getCanonicalName());
        }
        sendNotification(MBeanServerNotification.UNREGISTRATION_NOTIFICATION, name);
        if (object instanceof MBeanRegistration) {
            meta.postDeregisterInvoker(object);
        }
    }
    
    public ObjectInstance getObjectInstance(ObjectName name) throws InstanceNotFoundException {
        name = nonDefaultDomain(name);
        Object obj = getMBean(name);
        final String className;
        try {
            className = meta.getMBeanClassName(obj);
        } catch (IntrospectionException x) {
            debugX("getObjectInstance", x);
            throw new JMRuntimeException("Can\'t obtain class name for " + name + ": " + x);
        } catch (NotCompliantMBeanException x) {
            debugX("getObjectInstance", x);
            throw new JMRuntimeException("Can\'t obtain class name for " + name + ": " + x);
        }
        checkMBeanPermission(className, null, name, "getObjectInstance");
        return new ObjectInstance(name, className);
    }
    
    public Set queryMBeans(ObjectName name, QueryExp query) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            checkMBeanPermission(null, null, null, "queryMBeans");
            Set list = queryMBeansImpl(name, null);
            Set allowedList = new HashSet(list.size());
            for (Iterator i = list.iterator(); i.hasNext(); ) {
                try {
                    ObjectInstance oi = (ObjectInstance)(ObjectInstance)i.next();
                    checkMBeanPermission(oi.getClassName(), null, oi.getObjectName(), "queryMBeans");
                    allowedList.add(oi);
                } catch (SecurityException e) {
                }
            }
            return filterListOfObjectInstances(allowedList, query);
        } else {
            return queryMBeansImpl(name, query);
        }
    }
    
    private Set queryMBeansImpl(ObjectName name, QueryExp query) {
        Set list = null;
        synchronized (this) {
            list = repository.query(name, query);
        }
        if (queryByRepo) {
            return list;
        } else {
            return (filterListOfObjects(list, query));
        }
    }
    
    public Set queryNames(ObjectName name, QueryExp query) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            checkMBeanPermission(null, null, null, "queryNames");
            Set list = queryMBeansImpl(name, null);
            Set allowedList = new HashSet(list.size());
            for (Iterator i = list.iterator(); i.hasNext(); ) {
                try {
                    ObjectInstance oi = (ObjectInstance)(ObjectInstance)i.next();
                    checkMBeanPermission(oi.getClassName(), null, oi.getObjectName(), "queryNames");
                    allowedList.add(oi);
                } catch (SecurityException e) {
                }
            }
            Set queryList = filterListOfObjectInstances(allowedList, query);
            Set result = new HashSet(queryList.size());
            for (Iterator i = queryList.iterator(); i.hasNext(); ) {
                ObjectInstance oi = (ObjectInstance)(ObjectInstance)i.next();
                result.add(oi.getObjectName());
            }
            return result;
        } else {
            Set queryList = queryMBeansImpl(name, query);
            Set result = new HashSet(queryList.size());
            for (Iterator i = queryList.iterator(); i.hasNext(); ) {
                ObjectInstance oi = (ObjectInstance)(ObjectInstance)i.next();
                result.add(oi.getObjectName());
            }
            return result;
        }
    }
    
    public boolean isRegistered(ObjectName name) {
        if (name == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Object name cannot be null"), "Object name cannot be null");
        }
        name = nonDefaultDomain(name);
        synchronized (this) {
            return (repository.contains(name));
        }
    }
    
    public String[] getDomains() {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            checkMBeanPermission(null, null, null, "getDomains");
            String[] domains = repository.getDomains();
            ArrayList result = new ArrayList(domains.length);
            for (int i = 0; i < domains.length; i++) {
                try {
                    ObjectName domain = new ObjectName(domains[i] + ":x=x");
                    checkMBeanPermission(null, null, domain, "getDomains");
                    result.add(domains[i]);
                } catch (MalformedObjectNameException e) {
                    error("getDomains", "Failed to check permission for domain=" + domains[i] + ". Error is: " + e);
                    debugX("getDomains", e);
                } catch (SecurityException e) {
                }
            }
            return (String[])(String[])result.toArray(new String[result.size()]);
        } else {
            return repository.getDomains();
        }
    }
    
    public Integer getMBeanCount() {
        return (repository.getCount());
    }
    
    public Object getAttribute(ObjectName name, String attribute) throws MBeanException, AttributeNotFoundException, InstanceNotFoundException, ReflectionException {
        if (name == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Object name cannot be null"), "Exception occured trying to invoke the getter on the MBean");
        }
        if (attribute == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Attribute cannot be null"), "Exception occured trying to invoke the getter on the MBean");
        }
        name = nonDefaultDomain(name);
        if (isTraceOn()) {
            trace("getAttribute", "Attribute= " + attribute + ", obj= " + name);
        }
        Object instance = getMBean(name);
        String classname = null;
        try {
            classname = meta.getMBeanClassName(instance);
        } catch (IntrospectionException e) {
            classname = null;
        } catch (NotCompliantMBeanException e) {
            classname = null;
        }
        checkMBeanPermission(classname, attribute, name, "getAttribute");
        return meta.getAttribute(instance, attribute);
    }
    
    public AttributeList getAttributes(ObjectName name, String[] attributes) throws InstanceNotFoundException, ReflectionException {
        if (name == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("ObjectName name cannot be null"), "Exception occured trying to invoke the getter on the MBean");
        }
        if (attributes == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Attributes cannot be null"), "Exception occured trying to invoke the getter on the MBean");
        }
        name = nonDefaultDomain(name);
        if (isTraceOn()) {
            trace("getAttributes", "Object= " + name);
        }
        Object instance = getMBean(name);
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            String classname = null;
            try {
                classname = meta.getMBeanClassName(instance);
            } catch (IntrospectionException e) {
                classname = null;
            } catch (NotCompliantMBeanException e) {
                classname = null;
            }
            checkMBeanPermission(classname, null, name, "getAttribute");
            ArrayList allowedList = new ArrayList(attributes.length);
            for (int i = 0; i < attributes.length; i++) {
                try {
                    checkMBeanPermission(classname, attributes[i], name, "getAttribute");
                    allowedList.add(attributes[i]);
                } catch (SecurityException e) {
                }
            }
            String[] allowedAttributes = (String[])(String[])allowedList.toArray(new String[0]);
            return meta.getAttributes(instance, allowedAttributes);
        } else {
            return meta.getAttributes(instance, attributes);
        }
    }
    
    public void setAttribute(ObjectName name, Attribute attribute) throws InstanceNotFoundException, AttributeNotFoundException, InvalidAttributeValueException, MBeanException, ReflectionException {
        if (name == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("ObjectName name cannot be null"), "Exception occured trying to invoke the setter on the MBean");
        }
        if (attribute == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Attribute cannot be null"), "Exception occured trying to invoke the setter on the MBean");
        }
        name = nonDefaultDomain(name);
        if (isTraceOn()) {
            trace("setAttribute", "Object= " + name + ", attribute=" + attribute.getName());
        }
        Object instance = getMBean(name);
        String classname = null;
        try {
            classname = meta.getMBeanClassName(instance);
        } catch (IntrospectionException e) {
            classname = null;
        } catch (NotCompliantMBeanException e) {
            classname = null;
        }
        checkMBeanPermission(classname, attribute.getName(), name, "setAttribute");
        final Object o = meta.setAttribute(instance, attribute);
    }
    
    public AttributeList setAttributes(ObjectName name, AttributeList attributes) throws InstanceNotFoundException, ReflectionException {
        if (name == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("ObjectName name cannot be null"), "Exception occured trying to invoke the setter on the MBean");
        }
        if (attributes == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("AttributeList  cannot be null"), "Exception occured trying to invoke the setter on the MBean");
        }
        name = nonDefaultDomain(name);
        Object instance = getMBean(name);
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            String classname = null;
            try {
                classname = meta.getMBeanClassName(instance);
            } catch (IntrospectionException e) {
                classname = null;
            } catch (NotCompliantMBeanException e) {
                classname = null;
            }
            checkMBeanPermission(classname, null, name, "setAttribute");
            AttributeList allowedAttributes = new AttributeList(attributes.size());
            for (Iterator i = attributes.iterator(); i.hasNext(); ) {
                try {
                    Attribute attribute = (Attribute)(Attribute)i.next();
                    checkMBeanPermission(classname, attribute.getName(), name, "setAttribute");
                    allowedAttributes.add(attribute);
                } catch (SecurityException e) {
                }
            }
            return meta.setAttributes(instance, allowedAttributes);
        } else {
            return meta.setAttributes(instance, attributes);
        }
    }
    
    public Object invoke(ObjectName name, String operationName, Object[] params, String[] signature) throws InstanceNotFoundException, MBeanException, ReflectionException {
        name = nonDefaultDomain(name);
        Object instance = getMBean(name);
        String classname = null;
        try {
            classname = meta.getMBeanClassName(instance);
        } catch (IntrospectionException e) {
            classname = null;
        } catch (NotCompliantMBeanException e) {
            classname = null;
        }
        checkMBeanPermission(classname, operationName, name, "invoke");
        return meta.invoke(instance, operationName, params, signature);
    }
    
    protected MetaData meta() {
        return meta;
    }
    
    protected ObjectInstance makeObjectInstance(String className, Object object, ObjectName name) throws NotCompliantMBeanException {
        if (object instanceof DynamicMBean) {
            try {
                className = meta.getMBeanClassName(object);
            } catch (SecurityException x) {
                debugX("makeObjectInstance", x);
                throw x;
            } catch (IntrospectionException x) {
                debugX("makeObjectInstance", x);
                throw new NotCompliantMBeanException("Can\'t obtain class name for " + name + ": " + x);
            } catch (JMRuntimeException x) {
                debugX("makeObjectInstance", x);
                throw new NotCompliantMBeanException("Can\'t obtain class name for " + name + ": " + x);
            }
        }
        if (className == null) {
            throw new NotCompliantMBeanException("The class Name returned is null");
        }
        return (new ObjectInstance(nonDefaultDomain(name), className));
    }
    
    protected ObjectInstance registerObject(String classname, Object object, ObjectName name) throws InstanceAlreadyExistsException, MBeanRegistrationException, NotCompliantMBeanException {
        if (object == null) {
            final RuntimeException wrapped = new IllegalArgumentException("Cannot add null object");
            throw new RuntimeOperationsException(wrapped, "Exception occured trying to register the MBean");
        }
        name = nonDefaultDomain(name);
        if (isTraceOn()) {
            trace(dbgTag, "registerMBean", "ObjectName = " + name);
        }
        ObjectName logicalName = name;
        if (object instanceof MBeanRegistration) {
            logicalName = meta.preRegisterInvoker(object, name, server);
            if (logicalName != name && logicalName != null) {
                logicalName = ObjectName.getInstance(nonDefaultDomain(logicalName));
            }
        }
        checkMBeanPermission(classname, null, logicalName, "registerMBean");
        final ObjectInstance result;
        if (logicalName != null) {
            result = makeObjectInstance(classname, object, logicalName);
            internal_addObject(object, logicalName);
        } else {
            if (object instanceof MBeanRegistration) {
                meta.postRegisterInvoker(object, false);
            }
            final RuntimeException wrapped = new IllegalArgumentException("No object name specified");
            throw new RuntimeOperationsException(wrapped, "Exception occured trying to register the MBean");
        }
        if (object instanceof MBeanRegistration) meta.postRegisterInvoker(object, true);
        if (object instanceof ClassLoader) {
            final ModifiableClassLoaderRepository clr = instantiator.getClassLoaderRepository();
            if (clr == null) {
                final RuntimeException wrapped = new IllegalArgumentException("Dynamic addition of class loaders is not supported");
                throw new RuntimeOperationsException(wrapped, "Exception occured trying to register the MBean as a class loader");
            }
            clr.addClassLoader(logicalName, (ClassLoader)(ClassLoader)object);
        }
        return result;
    }
    
    protected ObjectInstance registerCreatedObject(String classname, Object object, ObjectName name) throws InstanceAlreadyExistsException, MBeanRegistrationException, NotCompliantMBeanException {
        return registerObject(classname, object, name);
    }
    
    private Object getMBean(ObjectName name) throws InstanceNotFoundException {
        if (name == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Object name cannot be null"), "Exception occured trying to get an MBean");
        }
        Object obj = null;
        synchronized (this) {
            obj = repository.retrieve(name);
            if (obj == null) {
                if (isTraceOn()) {
                    trace("getMBean", name + ": Found no object");
                }
                throw new InstanceNotFoundException(name.toString());
            }
        }
        return obj;
    }
    
    private ObjectName nonDefaultDomain(ObjectName name) {
        if (name == null || name.getDomain().length() > 0) return name;
        final String completeName = domain + name;
        try {
            return new ObjectName(completeName);
        } catch (MalformedObjectNameException e) {
            final String msg = "Unexpected default domain problem: " + completeName + ": " + e;
            throw new IllegalArgumentException(msg);
        }
    }
    
    public String getDefaultDomain() {
        return domain;
    }
    
    public void addNotificationListener(ObjectName name, NotificationListener listener, NotificationFilter filter, Object handback) throws InstanceNotFoundException {
        if (isTraceOn()) {
            trace("addNotificationListener", "obj= " + name);
        }
        Object instance = getMBean(name);
        String classname = null;
        try {
            classname = meta.getMBeanClassName(instance);
        } catch (IntrospectionException e) {
            classname = null;
        } catch (NotCompliantMBeanException e) {
            classname = null;
        }
        checkMBeanPermission(classname, null, name, "addNotificationListener");
        NotificationBroadcaster broadcaster;
        if (!(instance instanceof NotificationBroadcaster)) {
            throw new RuntimeOperationsException(new IllegalArgumentException(name.getCanonicalName()), "The MBean " + name.getCanonicalName() + " does not implement the NotificationBroadcaster interface");
        }
        broadcaster = (NotificationBroadcaster)(NotificationBroadcaster)instance;
        if (listener == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Null listener"), "Null listener");
        }
        NotificationListener listenerWrapper = getListenerWrapper(listener, name, instance, true);
        broadcaster.addNotificationListener(listenerWrapper, filter, handback);
    }
    
    public void addNotificationListener(ObjectName name, ObjectName listener, NotificationFilter filter, Object handback) throws InstanceNotFoundException {
        Object instance = getMBean(listener);
        if (!(instance instanceof NotificationListener)) {
            throw new RuntimeOperationsException(new IllegalArgumentException(listener.getCanonicalName()), "The MBean " + listener.getCanonicalName() + "does not implement the NotificationListener interface");
        }
        if (isTraceOn()) {
            trace("addNotificationListener", "obj= " + name + " listener= " + listener);
        }
        server.addNotificationListener(name, (NotificationListener)(NotificationListener)instance, filter, handback);
    }
    
    public void removeNotificationListener(ObjectName name, NotificationListener listener) throws InstanceNotFoundException, ListenerNotFoundException {
        removeNotificationListener(name, listener, null, null, true);
    }
    
    public void removeNotificationListener(ObjectName name, NotificationListener listener, NotificationFilter filter, Object handback) throws InstanceNotFoundException, ListenerNotFoundException {
        removeNotificationListener(name, listener, filter, handback, false);
    }
    
    public void removeNotificationListener(ObjectName name, ObjectName listener) throws InstanceNotFoundException, ListenerNotFoundException {
        NotificationListener instance = getListener(listener);
        if (isTraceOn()) {
            trace("removeNotificationListener", "obj= " + name + " listener= " + listener);
        }
        server.removeNotificationListener(name, instance);
    }
    
    public void removeNotificationListener(ObjectName name, ObjectName listener, NotificationFilter filter, Object handback) throws InstanceNotFoundException, ListenerNotFoundException {
        NotificationListener instance = getListener(listener);
        if (isTraceOn()) {
            trace("removeNotificationListener", "obj= " + name + " listener= " + listener);
        }
        server.removeNotificationListener(name, instance, filter, handback);
    }
    
    private NotificationListener getListener(ObjectName listener) throws ListenerNotFoundException {
        final Object instance;
        try {
            instance = getMBean(listener);
        } catch (InstanceNotFoundException e) {
            throw new ListenerNotFoundException(e.getMessage());
        }
        if (!(instance instanceof NotificationListener)) {
            final RuntimeException exc = new IllegalArgumentException(listener.getCanonicalName());
            final String msg = "MBean " + listener.getCanonicalName() + " does not " + "implement " + NotificationListener.class.getName();
            throw new RuntimeOperationsException(exc, msg);
        }
        return (NotificationListener)(NotificationListener)instance;
    }
    
    private void removeNotificationListener(ObjectName name, NotificationListener listener, NotificationFilter filter, Object handback, boolean removeAll) throws InstanceNotFoundException, ListenerNotFoundException {
        if (isTraceOn()) {
            trace("removeNotificationListener", "obj= " + name);
        }
        Object instance = getMBean(name);
        String classname = null;
        try {
            classname = meta.getMBeanClassName(instance);
        } catch (IntrospectionException e) {
            classname = null;
        } catch (NotCompliantMBeanException e) {
            classname = null;
        }
        checkMBeanPermission(classname, null, name, "removeNotificationListener");
        NotificationBroadcaster broadcaster = null;
        NotificationEmitter emitter = null;
        if (removeAll) {
            if (!(instance instanceof NotificationBroadcaster)) {
                final RuntimeException exc = new IllegalArgumentException(name.getCanonicalName());
                final String msg = "MBean " + name.getCanonicalName() + " does not " + "implement " + NotificationBroadcaster.class.getName();
                throw new RuntimeOperationsException(exc, msg);
            }
            broadcaster = (NotificationBroadcaster)(NotificationBroadcaster)instance;
        } else {
            if (!(instance instanceof NotificationEmitter)) {
                final RuntimeException exc = new IllegalArgumentException(name.getCanonicalName());
                final String msg = "MBean " + name.getCanonicalName() + " does not " + "implement " + NotificationEmitter.class.getName();
                throw new RuntimeOperationsException(exc, msg);
            }
            emitter = (NotificationEmitter)(NotificationEmitter)instance;
        }
        NotificationListener listenerWrapper = getListenerWrapper(listener, name, instance, false);
        if (listenerWrapper == null) throw new ListenerNotFoundException("Unknown listener");
        if (removeAll) broadcaster.removeNotificationListener(listenerWrapper); else {
            emitter.removeNotificationListener(listenerWrapper, filter, handback);
        }
    }
    
    public MBeanInfo getMBeanInfo(ObjectName name) throws InstanceNotFoundException, IntrospectionException, ReflectionException {
        Object moi = getMBean(name);
        final MBeanInfo mbi = meta.getMBeanInfo(moi);
        if (mbi == null) throw new JMRuntimeException("MBean " + name + "has no MBeanInfo");
        checkMBeanPermission(mbi.getClassName(), null, name, "getMBeanInfo");
        return mbi;
    }
    
    public boolean isInstanceOf(ObjectName name, String className) throws InstanceNotFoundException {
        Object instance = getMBean(name);
        String classname = null;
        try {
            classname = meta.getMBeanClassName(instance);
        } catch (IntrospectionException e) {
            classname = null;
        } catch (NotCompliantMBeanException e) {
            classname = null;
        }
        checkMBeanPermission(classname, null, name, "isInstanceOf");
        try {
            return meta.isInstanceOf(instance, className);
        } catch (ReflectionException e) {
            debugX("isInstanceOf", e);
            return false;
        }
    }
    
    public ClassLoader getClassLoaderFor(ObjectName mbeanName) throws InstanceNotFoundException {
        Object instance = getMBean(mbeanName);
        String classname = null;
        try {
            classname = meta.getMBeanClassName(instance);
        } catch (IntrospectionException e) {
            classname = null;
        } catch (NotCompliantMBeanException e) {
            classname = null;
        }
        checkMBeanPermission(classname, null, mbeanName, "getClassLoaderFor");
        return instance.getClass().getClassLoader();
    }
    
    public ClassLoader getClassLoader(ObjectName loaderName) throws InstanceNotFoundException {
        if (loaderName == null) {
            checkMBeanPermission(null, null, null, "getClassLoader");
            return server.getClass().getClassLoader();
        }
        Object instance = getMBean(loaderName);
        String classname = null;
        try {
            classname = meta.getMBeanClassName(instance);
        } catch (IntrospectionException e) {
            classname = null;
        } catch (NotCompliantMBeanException e) {
            classname = null;
        }
        checkMBeanPermission(classname, null, loaderName, "getClassLoader");
        if (!(instance instanceof ClassLoader)) throw new InstanceNotFoundException(loaderName.toString() + " is not a classloader");
        return (ClassLoader)(ClassLoader)instance;
    }
    
    private void internal_addObject(Object object, ObjectName logicalName) throws InstanceAlreadyExistsException {
        synchronized (this) {
            try {
                repository.addMBean(object, logicalName);
            } catch (InstanceAlreadyExistsException e) {
                if (object instanceof MBeanRegistration) {
                    meta.postRegisterInvoker(object, false);
                }
                throw e;
            }
        }
        if (isTraceOn()) {
            trace("addObject", "Send create notification of object " + logicalName.getCanonicalName());
        }
        sendNotification(MBeanServerNotification.REGISTRATION_NOTIFICATION, logicalName);
    }
    
    private void sendNotification(String NotifType, ObjectName name) {
        MBeanServerNotification notif = new MBeanServerNotification(NotifType, _MBSDelegateObjectName, 0, name);
        if (isTraceOn()) {
            trace("sendNotification", NotifType + " " + name);
        }
        delegate.sendNotification(notif);
    }
    
    private void initialize(String domain, MBeanServer outer, MBeanServerDelegate delegate, MBeanInstantiator inst, MetaData meta, Repository repos) {
        if (!this.domain.equals(repository.getDefaultDomain())) throw new IllegalArgumentException("Domain Name Mismatch");
        try {
            queryByRepo = repository.isFiltering();
        } catch (SecurityException e) {
            throw e;
        } catch (Exception e) {
            queryByRepo = false;
        }
    }
    
    private Set filterListOfObjects(Set list, QueryExp query) {
        Set result = new HashSet();
        if (query == null) {
            for (final Iterator i = list.iterator(); i.hasNext(); ) {
                final NamedObject no = (NamedObject)(NamedObject)i.next();
                final Object obj = no.getObject();
                String className = null;
                try {
                    className = meta.getMBeanClassName(obj);
                } catch (JMException x) {
                    if (isDebugOn()) {
                        debug("filterListOfObjects", "Can\'t obtain class name for " + no.getName() + ": " + x);
                        debugX("filterListOfObjects", x);
                    }
                }
                result.add(new ObjectInstance(no.getName(), className));
            }
        } else {
            for (final Iterator i = list.iterator(); i.hasNext(); ) {
                final NamedObject no = (NamedObject)(NamedObject)i.next();
                final Object obj = no.getObject();
                boolean res = false;
                MBeanServer oldServer = QueryEval.getMBeanServer();
                query.setMBeanServer(server);
                try {
                    res = query.apply(no.getName());
                } catch (Exception e) {
                    res = false;
                } finally {
                    query.setMBeanServer(oldServer);
                }
                if (res) {
                    String className = null;
                    try {
                        className = meta.getMBeanClassName(obj);
                    } catch (JMException x) {
                        if (isDebugOn()) {
                            debug("filterListOfObjects", "Can\'t obtain class name for " + no.getName() + ": " + x);
                            debugX("filterListOfObjects", x);
                        }
                    }
                    result.add(new ObjectInstance(no.getName(), className));
                }
            }
        }
        return result;
    }
    
    private Set filterListOfObjectInstances(Set list, QueryExp query) {
        if (query == null) {
            return list;
        } else {
            Set result = new HashSet();
            for (final Iterator i = list.iterator(); i.hasNext(); ) {
                final ObjectInstance oi = (ObjectInstance)(ObjectInstance)i.next();
                boolean res = false;
                MBeanServer oldServer = QueryEval.getMBeanServer();
                query.setMBeanServer(server);
                try {
                    res = query.apply(oi.getObjectName());
                } catch (Exception e) {
                    res = false;
                } finally {
                    query.setMBeanServer(oldServer);
                }
                if (res) {
                    result.add(oi);
                }
            }
            return result;
        }
    }
    
    private NotificationListener getListenerWrapper(NotificationListener l, ObjectName name, Object mbean, boolean create) {
        NotificationListener wrapper = new DefaultMBeanServerInterceptor$ListenerWrapper(l, name, mbean);
        synchronized (listenerWrappers) {
            WeakReference ref = (WeakReference)(WeakReference)listenerWrappers.get(wrapper);
            if (ref != null) {
                NotificationListener existing = (NotificationListener)(NotificationListener)ref.get();
                if (existing != null) return existing;
            }
            if (create) {
                listenerWrappers.put(wrapper, new WeakReference(wrapper));
                return wrapper;
            } else return null;
        }
    }
    {
    }
    
    private static void checkMBeanPermission(String classname, String member, ObjectName objectName, String actions) throws SecurityException {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            Permission perm = new MBeanPermission(classname, member, objectName, actions);
            sm.checkPermission(perm);
        }
    }
    
    private static void checkMBeanTrustPermission(final Class theClass) throws SecurityException {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            Permission perm = new MBeanTrustPermission("register");
            ProtectionDomain pd = (ProtectionDomain)(ProtectionDomain)AccessController.doPrivileged(new DefaultMBeanServerInterceptor$1(theClass));
            AccessControlContext acc = new AccessControlContext(new ProtectionDomain[]{pd});
            sm.checkPermission(perm, acc);
        }
    }
    
    private static boolean isTraceOn() {
        return Trace.isSelected(Trace.LEVEL_TRACE, Trace.INFO_MBEANSERVER);
    }
    
    private static void trace(String clz, String func, String info) {
        Trace.send(Trace.LEVEL_TRACE, Trace.INFO_MBEANSERVER, clz, func, info);
    }
    
    private static void trace(String func, String info) {
        trace(dbgTag, func, info);
    }
    
    private static void error(String func, String info) {
        Trace.send(Trace.LEVEL_ERROR, Trace.INFO_MBEANSERVER, dbgTag, func, info);
    }
    
    private static boolean isDebugOn() {
        return Trace.isSelected(Trace.LEVEL_DEBUG, Trace.INFO_MBEANSERVER);
    }
    
    private static void debug(String clz, String func, String info) {
        Trace.send(Trace.LEVEL_DEBUG, Trace.INFO_MBEANSERVER, clz, func, info);
    }
    
    private static void debug(String func, String info) {
        debug(dbgTag, func, info);
    }
    
    private static void debugX(String func, Throwable e) {
        if (isDebugOn()) {
            final StringWriter s = new StringWriter();
            e.printStackTrace(new PrintWriter(s));
            final String stack = s.toString();
            debug(dbgTag, func, "Exception caught in " + func + "(): " + e);
            debug(dbgTag, func, stack);
        }
    }
}
