package com.sun.jmx.mbeanserver;

import javax.management.*;

public interface MetaData {
    
    public void testCompliance(Class c) throws NotCompliantMBeanException;
    
    public ObjectName preRegisterInvoker(Object moi, ObjectName name, MBeanServer mbs) throws InstanceAlreadyExistsException, MBeanRegistrationException;
    
    public void postRegisterInvoker(Object moi, boolean registrationDone);
    
    public void preDeregisterInvoker(Object moi) throws MBeanRegistrationException;
    
    public void postDeregisterInvoker(Object moi);
    
    public MBeanInfo getMBeanInfo(Object instance) throws IntrospectionException;
    
    public String getMBeanClassName(Object instance) throws IntrospectionException, NotCompliantMBeanException;
    
    public Object getAttribute(Object instance, String attribute) throws MBeanException, AttributeNotFoundException, ReflectionException;
    
    public AttributeList getAttributes(Object instance, String[] attributes) throws ReflectionException;
    
    public Object setAttribute(Object instance, Attribute attribute) throws AttributeNotFoundException, InvalidAttributeValueException, MBeanException, ReflectionException;
    
    public AttributeList setAttributes(Object instance, AttributeList attributes) throws ReflectionException;
    
    public Object invoke(Object instance, String operationName, Object[] params, String[] signature) throws MBeanException, ReflectionException;
    
    public boolean isInstanceOf(Object instance, String className) throws ReflectionException;
}
