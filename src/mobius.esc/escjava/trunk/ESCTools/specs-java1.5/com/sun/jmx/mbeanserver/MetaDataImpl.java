package com.sun.jmx.mbeanserver;

import java.io.PrintWriter;
import java.io.StringWriter;
import javax.management.*;
import com.sun.jmx.trace.Trace;

public class MetaDataImpl implements MetaData {
    private static final String dbgTag = "MetaDataImpl";
    private final DynamicMetaDataImpl dynamic;
    private final StandardMetaDataImpl standard;
    protected final MBeanInstantiator instantiator;
    {
    }
    {
    }
    
    public MetaDataImpl(MBeanInstantiator instantiator) {
        
        if (instantiator == null) throw new IllegalArgumentException("instantiator must not be null.");
        this.instantiator = instantiator;
        this.dynamic = new MetaDataImpl$PrivateDynamicMeta(this);
        this.standard = new MetaDataImpl$PrivateStandardMeta(this);
    }
    
    protected MetaData getMetaData(Class c) {
        if (DynamicMBean.class.isAssignableFrom(c)) return dynamic; else return standard;
    }
    
    protected MetaData getMetaData(Object moi) {
        if (moi instanceof DynamicMBean) return dynamic; else return standard;
    }
    
    public synchronized void testCompliance(Class c) throws NotCompliantMBeanException {
        final MetaData meta = getMetaData(c);
        meta.testCompliance(c);
    }
    
    public Class getMBeanInterfaceFromClass(Class c) {
        return standard.getMBeanInterfaceFromClass(c);
    }
    
    public MBeanInfo getMBeanInfoFromClass(Class beanClass) throws IntrospectionException, NotCompliantMBeanException {
        return standard.getMBeanInfoFromClass(beanClass);
    }
    
    public final String getMBeanClassName(Object moi) throws IntrospectionException, NotCompliantMBeanException {
        final MetaData meta = getMetaData(moi);
        return meta.getMBeanClassName(moi);
    }
    
    public final MBeanInfo getMBeanInfo(Object moi) throws IntrospectionException {
        final MetaData meta = getMetaData(moi);
        return meta.getMBeanInfo(moi);
    }
    
    public final Object getAttribute(Object instance, String attribute) throws MBeanException, AttributeNotFoundException, ReflectionException {
        final MetaData meta = getMetaData(instance);
        return meta.getAttribute(instance, attribute);
    }
    
    public final AttributeList getAttributes(Object instance, String[] attributes) throws ReflectionException {
        final MetaData meta = getMetaData(instance);
        return meta.getAttributes(instance, attributes);
    }
    
    public final AttributeList setAttributes(Object instance, AttributeList attributes) throws ReflectionException {
        final MetaData meta = getMetaData(instance);
        return meta.setAttributes(instance, attributes);
    }
    
    public final Object setAttribute(Object instance, Attribute attribute) throws AttributeNotFoundException, InvalidAttributeValueException, MBeanException, ReflectionException {
        final MetaData meta = getMetaData(instance);
        return meta.setAttribute(instance, attribute);
    }
    
    public final Object invoke(Object instance, String operationName, Object[] params, String[] signature) throws MBeanException, ReflectionException {
        if (operationName == null) {
            final RuntimeException r = new IllegalArgumentException("Operation name cannot be null");
            throw new RuntimeOperationsException(r, "Exception occured trying to invoke the operation on the MBean");
        }
        final MetaData meta = getMetaData(instance);
        return meta.invoke(instance, operationName, params, signature);
    }
    
    public boolean isInstanceOf(Object instance, String className) throws ReflectionException {
        final MetaData meta = getMetaData(instance);
        return meta.isInstanceOf(instance, className);
    }
    
    public ObjectName preRegisterInvoker(Object moi, ObjectName name, MBeanServer mbs) throws InstanceAlreadyExistsException, MBeanRegistrationException {
        if (!(moi instanceof MBeanRegistration)) return name;
        final MetaData meta = getMetaData(moi);
        return meta.preRegisterInvoker(moi, name, mbs);
    }
    
    public void postRegisterInvoker(Object moi, boolean registrationDone) {
        if (!(moi instanceof MBeanRegistration)) return;
        final MetaData meta = getMetaData(moi);
        meta.postRegisterInvoker(moi, registrationDone);
    }
    
    public void preDeregisterInvoker(Object moi) throws MBeanRegistrationException {
        if (!(moi instanceof MBeanRegistration)) return;
        final MetaData meta = getMetaData(moi);
        meta.preDeregisterInvoker(moi);
    }
    
    public void postDeregisterInvoker(Object moi) {
        if (!(moi instanceof MBeanRegistration)) return;
        final MetaData meta = getMetaData(moi);
        meta.postDeregisterInvoker(moi);
    }
    
    protected Class findClass(String className, ClassLoader loader) throws ReflectionException {
        return instantiator.findClass(className, loader);
    }
    
    protected Class[] findSignatureClasses(String[] signature, ClassLoader loader) throws ReflectionException {
        return ((signature == null) ? null : instantiator.findSignatureClasses(signature, loader));
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
