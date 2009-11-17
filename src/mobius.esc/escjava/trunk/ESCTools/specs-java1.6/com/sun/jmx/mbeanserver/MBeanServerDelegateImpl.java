package com.sun.jmx.mbeanserver;

import javax.management.ObjectName;
import javax.management.MBeanServer;
import javax.management.MBeanRegistration;
import javax.management.DynamicMBean;
import javax.management.AttributeNotFoundException;
import javax.management.MBeanException;
import javax.management.ReflectionException;
import javax.management.MBeanAttributeInfo;
import javax.management.MBeanInfo;
import javax.management.JMRuntimeException;
import javax.management.InvalidAttributeValueException;
import javax.management.Attribute;
import javax.management.AttributeList;
import javax.management.RuntimeOperationsException;
import com.sun.jmx.defaults.ServiceName;
import com.sun.jmx.trace.Trace;

final class MBeanServerDelegateImpl extends javax.management.MBeanServerDelegate implements DynamicMBean, MBeanRegistration {
    private static final String dbgTag = "MBeanServerDelegateImpl";
    private static final String[] attributeNames = new String[]{"MBeanServerId", "SpecificationName", "SpecificationVersion", "SpecificationVendor", "ImplementationName", "ImplementationVersion", "ImplementationVendor"};
    private static final MBeanAttributeInfo[] attributeInfos = new MBeanAttributeInfo[]{new MBeanAttributeInfo("MBeanServerId", "java.lang.String", "The MBean server agent identification", true, false, false), new MBeanAttributeInfo("SpecificationName", "java.lang.String", "The full name of the JMX specification implemented by this product.", true, false, false), new MBeanAttributeInfo("SpecificationVersion", "java.lang.String", "The version of the JMX specification implemented by this product.", true, false, false), new MBeanAttributeInfo("SpecificationVendor", "java.lang.String", "The vendor of the JMX specification implemented by this product.", true, false, false), new MBeanAttributeInfo("ImplementationName", "java.lang.String", "The JMX implementation name (the name of this product)", true, false, false), new MBeanAttributeInfo("ImplementationVersion", "java.lang.String", "The JMX implementation version (the version of this product).", true, false, false), new MBeanAttributeInfo("ImplementationVendor", "java.lang.String", "the JMX implementation vendor (the vendor of this product).", true, false, false)};
    private final MBeanInfo delegateInfo;
    
    public MBeanServerDelegateImpl() {
        
        delegateInfo = new MBeanInfo("javax.management.MBeanServerDelegate", "Represents  the MBean server from the management point of view.", MBeanServerDelegateImpl.attributeInfos, null, null, getNotificationInfo());
    }
    
    public final ObjectName preRegister(MBeanServer server, ObjectName name) throws java.lang.Exception {
        if (name == null) return new ObjectName(ServiceName.DELEGATE); else return name;
    }
    
    public final void postRegister(Boolean registrationDone) {
    }
    
    public final void preDeregister() throws java.lang.Exception {
        throw new IllegalArgumentException("The MBeanServerDelegate MBean cannot be unregistered");
    }
    
    public final void postDeregister() {
    }
    
    public Object getAttribute(String attribute) throws AttributeNotFoundException, MBeanException, ReflectionException {
        try {
            if (attribute == null) throw new AttributeNotFoundException("null");
            if (attribute.equals("MBeanServerId")) return getMBeanServerId(); else if (attribute.equals("SpecificationName")) return getSpecificationName(); else if (attribute.equals("SpecificationVersion")) return getSpecificationVersion(); else if (attribute.equals("SpecificationVendor")) return getSpecificationVendor(); else if (attribute.equals("ImplementationName")) return getImplementationName(); else if (attribute.equals("ImplementationVersion")) return getImplementationVersion(); else if (attribute.equals("ImplementationVendor")) return getImplementationVendor(); else throw new AttributeNotFoundException("null");
        } catch (AttributeNotFoundException x) {
            throw x;
        } catch (JMRuntimeException j) {
            throw j;
        } catch (SecurityException s) {
            throw s;
        } catch (Exception x) {
            throw new MBeanException(x, "Failed to get " + attribute);
        }
    }
    
    public void setAttribute(Attribute attribute) throws AttributeNotFoundException, InvalidAttributeValueException, MBeanException, ReflectionException {
        final String attname = (attribute == null ? null : attribute.getName());
        if (attname == null) {
            final RuntimeException r = new IllegalArgumentException("Attribute name cannot be null");
            throw new RuntimeOperationsException(r, "Exception occured trying to invoke the setter on the MBean");
        }
        Object val = getAttribute(attname);
        throw new AttributeNotFoundException(attname + " not accessible");
    }
    
    public AttributeList getAttributes(String[] attributes) {
        final String[] attn = (attributes == null ? attributeNames : attributes);
        final int len = attn.length;
        final AttributeList list = new AttributeList(len);
        for (int i = 0; i < len; i++) {
            try {
                final Attribute a = new Attribute(attn[i], getAttribute(attn[i]));
                list.add(a);
            } catch (Exception x) {
                debug("getAttributes", "Attribute " + attn[i] + " not found.");
            }
        }
        return list;
    }
    
    public AttributeList setAttributes(AttributeList attributes) {
        return new AttributeList(0);
    }
    
    public Object invoke(String actionName, Object[] params, String[] signature) throws MBeanException, ReflectionException {
        if (actionName == null) {
            final RuntimeException r = new IllegalArgumentException("Operation name  cannot be null");
            throw new RuntimeOperationsException(r, "Exception occured trying to invoke the operation on the MBean");
        }
        throw new ReflectionException(new NoSuchMethodException(actionName), "The operation with name " + actionName + " could not be found");
    }
    
    public MBeanInfo getMBeanInfo() {
        return delegateInfo;
    }
    
    private static final boolean isTraceOn() {
        return Trace.isSelected(Trace.LEVEL_TRACE, Trace.INFO_MBEANSERVER);
    }
    
    private static final void trace(String clz, String func, String info) {
        Trace.send(Trace.LEVEL_TRACE, Trace.INFO_MBEANSERVER, clz, func, info);
    }
    
    private static final void trace(String func, String info) {
        trace(dbgTag, func, info);
    }
    
    private static final boolean isDebugOn() {
        return Trace.isSelected(Trace.LEVEL_DEBUG, Trace.INFO_MBEANSERVER);
    }
    
    private static final void debug(String clz, String func, String info) {
        Trace.send(Trace.LEVEL_DEBUG, Trace.INFO_MBEANSERVER, clz, func, info);
    }
    
    private static final void debug(String func, String info) {
        debug(dbgTag, func, info);
    }
}
