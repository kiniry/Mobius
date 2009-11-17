package com.sun.jmx.mbeanserver;

import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;
import java.util.Iterator;
import javax.management.IntrospectionException;
import javax.management.MBeanAttributeInfo;
import javax.management.MBeanConstructorInfo;
import javax.management.MBeanInfo;
import javax.management.MBeanOperationInfo;
import javax.management.NotCompliantMBeanException;

public class Introspector {
    private static final String attributeDescription = "Attribute exposed for management";
    private static final String operationDescription = "Operation exposed for management";
    private static final String constructorDescription = "Public constructor of the MBean";
    private static final String mbeanInfoDescription = "Information on the management interface of the MBean";
    
    private Introspector() {
        
    }
    
    public static final boolean isDynamic(final Class c) {
        return javax.management.DynamicMBean.class.isAssignableFrom(c);
    }
    
    public static void testCreation(Class c) throws NotCompliantMBeanException {
        final int mods = c.getModifiers();
        if (Modifier.isAbstract(mods) || Modifier.isInterface(mods)) {
            throw new NotCompliantMBeanException("MBean class must be concrete");
        }
        final Constructor[] consList = c.getConstructors();
        if (consList.length == 0) {
            throw new NotCompliantMBeanException("MBean class must have public constructor");
        }
    }
    
    public static MBeanInfo testCompliance(Class baseClass) throws NotCompliantMBeanException {
        if (isDynamic(baseClass)) return null;
        return testCompliance(baseClass, null);
    }
    
    static MBeanInfo testCompliance(final Class baseClass, Class mbeanInterface) throws NotCompliantMBeanException {
        if (baseClass.isInterface()) throw new NotCompliantMBeanException(baseClass.getName() + " must be a class.");
        if (mbeanInterface == null) mbeanInterface = getStandardMBeanInterface(baseClass); else if (!mbeanInterface.isAssignableFrom(baseClass)) {
            final String msg = baseClass.getName() + " does not implement the " + mbeanInterface.getName() + " interface";
            throw new NotCompliantMBeanException(msg);
        } else if (!mbeanInterface.isInterface()) {
            final String msg = baseClass.getName() + ": " + mbeanInterface.getName() + " is not an interface";
            throw new NotCompliantMBeanException(msg);
        }
        if (mbeanInterface == null) {
            final String baseClassName = baseClass.getName();
            final String msg = baseClassName + " does not implement the " + baseClassName + "MBean interface or the DynamicMBean interface";
            throw new NotCompliantMBeanException(msg);
        }
        final int mods = mbeanInterface.getModifiers();
        if (!Modifier.isPublic(mods)) throw new NotCompliantMBeanException(mbeanInterface.getName() + " implemented by " + baseClass.getName() + " must be public");
        return (introspect(baseClass, mbeanInterface));
    }
    
    public static Class getMBeanInterface(Class baseClass) {
        if (isDynamic(baseClass)) return null;
        return getStandardMBeanInterface(baseClass);
    }
    
    static Class getStandardMBeanInterface(Class baseClass) {
        Class current = baseClass;
        Class mbeanInterface = null;
        while (current != null) {
            mbeanInterface = findMBeanInterface(current, current.getName());
            if (mbeanInterface != null) break;
            current = current.getSuperclass();
        }
        return mbeanInterface;
    }
    
    private static Class findMBeanInterface(Class aClass, String aName) {
        Class current = aClass;
        while (current != null) {
            final Class[] interfaces = current.getInterfaces();
            final int len = interfaces.length;
            for (int i = 0; i < len; i++) {
                final Class inter = implementsMBean(interfaces[i], aName);
                if (inter != null) return inter;
            }
            current = current.getSuperclass();
        }
        return null;
    }
    
    private static MBeanInfo introspect(Class baseClass, Class beanClass) throws NotCompliantMBeanException {
        List attributes = new ArrayList();
        List operations = new ArrayList();
        Method[] methodList = beanClass.getMethods();
        for (int i = 0; i < methodList.length; i++) {
            Method method = methodList[i];
            String name = method.getName();
            Class[] argTypes = method.getParameterTypes();
            Class resultType = method.getReturnType();
            int argCount = argTypes.length;
            try {
                final MBeanAttributeInfo attr;
                if (name.startsWith("get") && !name.equals("get") && argCount == 0 && !resultType.equals(Void.TYPE)) {
                    attr = new MBeanAttributeInfo(name.substring(3), attributeDescription, method, null);
                } else if (name.startsWith("set") && !name.equals("set") && argCount == 1 && resultType.equals(Void.TYPE)) {
                    attr = new MBeanAttributeInfo(name.substring(3), attributeDescription, null, method);
                } else if (name.startsWith("is") && !name.equals("is") && argCount == 0 && resultType.equals(Boolean.TYPE)) {
                    attr = new MBeanAttributeInfo(name.substring(2), attributeDescription, method, null);
                } else {
                    attr = null;
                }
                if (attr != null) {
                    if (testConsistency(attributes, attr)) attributes.add(attr);
                } else {
                    final MBeanOperationInfo oper = new MBeanOperationInfo(operationDescription, method);
                    operations.add(oper);
                }
            } catch (IntrospectionException e) {
                error("introspect", e);
            }
        }
        return constructResult(baseClass, attributes, operations);
    }
    
    private static boolean testConsistency(List attributes, MBeanAttributeInfo attr) throws NotCompliantMBeanException {
        for (Iterator it = attributes.iterator(); it.hasNext(); ) {
            MBeanAttributeInfo mb = (MBeanAttributeInfo)(MBeanAttributeInfo)it.next();
            if (mb.getName().equals(attr.getName())) {
                if ((attr.isReadable() && mb.isReadable()) && (attr.isIs() != mb.isIs())) {
                    final String msg = "Conflicting getters for attribute " + mb.getName();
                    throw new NotCompliantMBeanException(msg);
                }
                if (!mb.getType().equals(attr.getType())) {
                    if (mb.isWritable() && attr.isWritable()) {
                        final String msg = "Type mismatch between parameters of set" + mb.getName() + " methods";
                        throw new NotCompliantMBeanException(msg);
                    } else {
                        final String msg = "Type mismatch between parameters of get or is" + mb.getName() + ", set" + mb.getName() + " methods";
                        throw new NotCompliantMBeanException(msg);
                    }
                }
                if (attr.isReadable() && mb.isReadable()) {
                    return false;
                }
                if (attr.isWritable() && mb.isWritable()) {
                    return false;
                }
            }
        }
        return true;
    }
    
    static MBeanConstructorInfo[] getConstructors(Class baseClass) {
        Constructor[] consList = baseClass.getConstructors();
        List constructors = new ArrayList();
        for (int i = 0; i < consList.length; i++) {
            Constructor constructor = consList[i];
            MBeanConstructorInfo mc = null;
            try {
                mc = new MBeanConstructorInfo(constructorDescription, constructor);
            } catch (Exception ex) {
                mc = null;
            }
            if (mc != null) {
                constructors.add(mc);
            }
        }
        MBeanConstructorInfo[] resultConstructors = new MBeanConstructorInfo[constructors.size()];
        constructors.toArray(resultConstructors);
        return resultConstructors;
    }
    
    private static MBeanInfo constructResult(Class baseClass, List attributes, List operations) {
        final int len = attributes.size();
        final MBeanAttributeInfo[] attrlist = new MBeanAttributeInfo[len];
        attributes.toArray(attrlist);
        final ArrayList mergedAttributes = new ArrayList();
        for (int i = 0; i < len; i++) {
            final MBeanAttributeInfo bi = attrlist[i];
            if (bi == null) continue;
            MBeanAttributeInfo att = bi;
            for (int j = i + 1; j < len; j++) {
                MBeanAttributeInfo mi = attrlist[j];
                if (mi == null) continue;
                if (mi.getName().compareTo(bi.getName()) == 0) {
                    attrlist[j] = null;
                    att = new MBeanAttributeInfo(bi.getName(), bi.getType(), attributeDescription, true, true, bi.isIs());
                }
            }
            mergedAttributes.add(att);
        }
        final MBeanAttributeInfo[] resultAttributes = new MBeanAttributeInfo[mergedAttributes.size()];
        mergedAttributes.toArray(resultAttributes);
        final MBeanOperationInfo[] resultOperations = new MBeanOperationInfo[operations.size()];
        operations.toArray(resultOperations);
        final MBeanConstructorInfo[] resultConstructors = getConstructors(baseClass);
        final MBeanInfo resultMBeanInfo = new MBeanInfo(baseClass.getName(), mbeanInfoDescription, resultAttributes, resultConstructors, resultOperations, null);
        return resultMBeanInfo;
    }
    
    static Class implementsMBean(Class c, String clName) {
        if (c.getName().compareTo(clName + "MBean") == 0) {
            return c;
        }
        Class current = c;
        Class[] interfaces = c.getInterfaces();
        for (int i = 0; i < interfaces.length; i++) {
            try {
                if (interfaces[i].getName().compareTo(clName + "MBean") == 0) {
                    return interfaces[i];
                }
            } catch (Exception e) {
                return null;
            }
        }
        return null;
    }
    
    private static void error(String method, Throwable t) {
        com.sun.jmx.trace.Trace.send(com.sun.jmx.trace.Trace.LEVEL_ERROR, com.sun.jmx.trace.Trace.INFO_MBEANSERVER, "Introspector", method, t);
    }
}
