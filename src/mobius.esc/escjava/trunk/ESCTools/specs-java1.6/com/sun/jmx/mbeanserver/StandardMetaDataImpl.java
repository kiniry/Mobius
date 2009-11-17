package com.sun.jmx.mbeanserver;

import java.lang.reflect.Method;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.ref.WeakReference;
import java.security.AccessController;
import java.util.Hashtable;
import java.util.Iterator;
import java.io.PrintWriter;
import java.io.StringWriter;
import javax.management.*;
import com.sun.jmx.trace.Trace;
import com.sun.jmx.mbeanserver.GetPropertyAction;

class StandardMetaDataImpl extends BaseMetaDataImpl {
    private static final String dbgTag = "StandardMetaDataImpl";
    private static java.util.Map mbeanInfoCache = new java.util.WeakHashMap();
    private static java.util.Map mbeanInterfaceCache = new java.util.WeakHashMap();
    private final boolean wrapRuntimeExceptions;
    private static final Hashtable primitiveClasses = new Hashtable(8);
    {
        primitiveClasses.put(Boolean.TYPE.toString(), Boolean.TYPE);
        primitiveClasses.put(Character.TYPE.toString(), Character.TYPE);
        primitiveClasses.put(Byte.TYPE.toString(), Byte.TYPE);
        primitiveClasses.put(Short.TYPE.toString(), Short.TYPE);
        primitiveClasses.put(Integer.TYPE.toString(), Integer.TYPE);
        primitiveClasses.put(Long.TYPE.toString(), Long.TYPE);
        primitiveClasses.put(Float.TYPE.toString(), Float.TYPE);
        primitiveClasses.put(Double.TYPE.toString(), Double.TYPE);
    }
    
    public StandardMetaDataImpl() {
        this(true);
    }
    
    StandardMetaDataImpl(boolean wrapRuntimeExceptions) {
        
        this.wrapRuntimeExceptions = wrapRuntimeExceptions;
    }
    
    public synchronized MBeanInfo buildMBeanInfo(Class c) throws NotCompliantMBeanException {
        return Introspector.testCompliance(c);
    }
    
    public synchronized MBeanInfo buildMBeanInfo(Class c, Class mbeanInterface) throws NotCompliantMBeanException {
        return Introspector.testCompliance(c, mbeanInterface);
    }
    
    public synchronized void testCompliance(Class c) throws NotCompliantMBeanException {
        final MBeanInfo mbeanInfo = buildMBeanInfo(c);
        final Class mbeanInterface = Introspector.getMBeanInterface(c);
        cacheMBeanInfo(c, mbeanInterface, mbeanInfo);
    }
    
    public synchronized void testCompliance(Class c, Class mbeanInterface) throws NotCompliantMBeanException {
        final MBeanInfo mbeanInfo = buildMBeanInfo(c, mbeanInterface);
        if (mbeanInterface == null) mbeanInterface = Introspector.getStandardMBeanInterface(c);
        cacheMBeanInfo(c, mbeanInterface, mbeanInfo);
    }
    
    public Class getMBeanInterfaceFromClass(Class c) {
        final Class itf = getCachedMBeanInterface(c);
        if (itf != null) return itf;
        synchronized (this) {
            return Introspector.getMBeanInterface(c);
        }
    }
    
    public Class getStandardMBeanInterface(Class c) {
        synchronized (this) {
            return Introspector.getStandardMBeanInterface(c);
        }
    }
    
    public MBeanInfo getMBeanInfoFromClass(Class beanClass) throws IntrospectionException, NotCompliantMBeanException {
        MBeanInfo bi = getCachedMBeanInfo(beanClass);
        if (bi != null) return (MBeanInfo)(MBeanInfo)bi.clone();
        testCompliance(beanClass);
        bi = getCachedMBeanInfo(beanClass);
        ;
        if (bi != null) return (MBeanInfo)(MBeanInfo)bi.clone();
        return bi;
    }
    
    public String getMBeanClassName(Object moi) throws IntrospectionException, NotCompliantMBeanException {
        return moi.getClass().getName();
    }
    
    public MBeanInfo getMBeanInfo(Object moi) throws IntrospectionException {
        try {
            final MBeanInfo mbi = getMBeanInfoFromClass(moi.getClass());
            return new MBeanInfo(mbi.getClassName(), mbi.getDescription(), mbi.getAttributes(), mbi.getConstructors(), mbi.getOperations(), findNotifications(moi));
        } catch (NotCompliantMBeanException x) {
            debugX("getMBeanInfo", x);
            throw new IntrospectionException("Can\'t build MBeanInfo for " + moi.getClass().getName());
        }
    }
    
    public Object getAttribute(Object instance, String attribute) throws MBeanException, AttributeNotFoundException, ReflectionException {
        Class mbeanClass = getMBeanInterfaceFromInstance(instance);
        if (isDebugOn()) {
            debug("getAttribute", "MBean Class is " + instance.getClass());
            debug("getAttribute", "MBean Interface is " + mbeanClass);
        }
        return getAttribute(instance, attribute, mbeanClass);
    }
    
    public AttributeList getAttributes(Object instance, String[] attributes) throws ReflectionException {
        final Class mbeanClass = getMBeanInterfaceFromInstance(instance);
        if (isDebugOn()) {
            debug("getAttributes", "MBean Class is " + instance.getClass());
            debug("getAttributes", "MBean Interface is " + mbeanClass);
        }
        if (attributes == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Attributes cannot be null"), "Exception occured trying to invoke the getter on the MBean");
        }
        final int maxLimit = attributes.length;
        final AttributeList result = new AttributeList(maxLimit);
        for (int i = 0; i < maxLimit; i++) {
            final String elmt = (String)attributes[i];
            try {
                final Object value = getAttribute(instance, elmt, mbeanClass);
                result.add(new Attribute(elmt, value));
            } catch (Exception excep) {
                if (isDebugOn()) {
                    debug("getAttributes", "Object= " + instance + ", Attribute=" + elmt + " failed: " + excep);
                }
            }
        }
        return result;
    }
    
    public AttributeList setAttributes(Object instance, AttributeList attributes) throws ReflectionException {
        final Class objClass = instance.getClass();
        final Class mbeanClass = getMBeanInterfaceFromInstance(instance);
        final ClassLoader aLoader = objClass.getClassLoader();
        if (isDebugOn()) {
            debug("setAttributes", "MBean Class is " + instance.getClass());
            debug("setAttributes", "MBean Interface is " + mbeanClass);
        }
        if (attributes == null) return new AttributeList();
        final AttributeList result = new AttributeList(attributes.size());
        for (final Iterator i = attributes.iterator(); i.hasNext(); ) {
            final Attribute attr = (Attribute)(Attribute)i.next();
            final String id = attr.getName();
            final Object value = attr.getValue();
            try {
                final Object newValue = setAttribute(instance, attr, mbeanClass);
                if (isTraceOn()) {
                    trace("setAttributes", "Updating the list\n");
                }
                result.add(new Attribute(id, newValue));
            } catch (Exception excep) {
                if (isDebugOn()) {
                    debug("setAttributes", "Unexpected exception occured: " + excep.getClass().getName());
                }
            }
        }
        return result;
    }
    
    public Object setAttribute(Object instance, Attribute attribute) throws AttributeNotFoundException, InvalidAttributeValueException, MBeanException, ReflectionException {
        final Class mbeanClass = getMBeanInterfaceFromInstance(instance);
        if (isDebugOn()) {
            debug("setAttribute", "MBean Class is " + instance.getClass());
            debug("setAttribute", "MBean Interface is " + mbeanClass);
        }
        return setAttribute(instance, attribute, mbeanClass);
    }
    
    public Object invoke(Object instance, String operationName, Object[] params, String[] signature) throws MBeanException, ReflectionException {
        if (operationName == null) {
            final RuntimeException r = new IllegalArgumentException("Operation name cannot be null");
            throw new RuntimeOperationsException(r, "Exception occured trying to invoke the operation on the MBean");
        }
        final Class objClass = instance.getClass();
        final Class mbeanClass = getMBeanInterfaceFromInstance(instance);
        final ClassLoader aLoader = objClass.getClassLoader();
        if (isDebugOn()) {
            debug("invoke", "MBean Class is " + instance.getClass());
            debug("invoke", "MBean Interface is " + mbeanClass);
        }
        final Class[] tab = ((signature == null) ? null : findSignatureClasses(signature, aLoader));
        Method mth = findMethod(mbeanClass, operationName, tab);
        if (mth == null) {
            if (isTraceOn()) {
                trace("invoke", operationName + " not found in class " + mbeanClass.getName());
            }
            throw new ReflectionException(new NoSuchMethodException(operationName), "The operation with name " + operationName + " could not be found");
        }
        forbidInvokeGetterSetter(mth, operationName);
        if (isTraceOn()) {
            trace("invoke", "Invoking " + operationName);
        }
        Object result = null;
        try {
            result = mth.invoke(instance, params);
        } catch (IllegalAccessException e) {
            debugX("invoke", e);
            throw new ReflectionException(e, "IllegalAccessException" + " occured trying to invoke operation " + operationName);
        } catch (RuntimeException e) {
            debugX("invoke", e);
            throw new RuntimeOperationsException(e, "RuntimeException" + " occured trying to invoke operation " + operationName);
        } catch (InvocationTargetException e) {
            Throwable t = e.getTargetException();
            debugX("invoke", t);
            if (t instanceof RuntimeException) {
                final String msg = "RuntimeException thrown in operation " + operationName;
                throw wrapRuntimeException((RuntimeException)(RuntimeException)t, msg);
            } else if (t instanceof Error) {
                throw new RuntimeErrorException((Error)(Error)t, "Error thrown in operation " + operationName);
            } else {
                throw new MBeanException((Exception)(Exception)t, "Exception thrown in operation " + operationName);
            }
        }
        if (isTraceOn()) {
            trace("invoke", "Send the result");
        }
        return (result);
    }
    
    private static boolean startsWithAndHasMore(String s, String prefix) {
        return (s.startsWith(prefix) && s.length() > prefix.length());
    }
    
    private static void forbidInvokeGetterSetter(Method mth, String operationName) throws ReflectionException {
        final Class[] argTypes = mth.getParameterTypes();
        final Class resultType = mth.getReturnType();
        final int argCount = argTypes.length;
        boolean isInvokeGetterSetter = false;
        switch (argCount) {
        case 0: 
            if ((startsWithAndHasMore(operationName, "get") && resultType != Void.TYPE) || (startsWithAndHasMore(operationName, "is") && resultType == Boolean.TYPE)) {
                isInvokeGetterSetter = true;
            }
            break;
        
        case 1: 
            if (startsWithAndHasMore(operationName, "set") && resultType == Void.TYPE) {
                isInvokeGetterSetter = true;
            }
            break;
        
        }
        if (isInvokeGetterSetter) {
            boolean allow;
            try {
                GetPropertyAction getProp = new GetPropertyAction("jmx.invoke.getters");
                allow = (AccessController.doPrivileged(getProp) != null);
            } catch (SecurityException e) {
                allow = false;
            }
            if (!allow) {
                final String msg = "Cannot invoke getter or setter (" + operationName + ") as operation unless jmx.invoke.getters property is set";
                final Exception nested = new NoSuchMethodException(operationName);
                throw new ReflectionException(nested, msg);
            }
        }
    }
    
    public boolean isInstanceOf(Object instance, String className) throws ReflectionException {
        final Class c = findClass(className, instance.getClass().getClassLoader());
        return c.isInstance(instance);
    }
    
    Class getMBeanInterfaceFromInstance(Object instance) {
        if (instance == null) return null;
        return getMBeanInterfaceFromClass(instance.getClass());
    }
    
    void cacheMBeanInfo(Class c, Class mbeanInterface, MBeanInfo info) throws NotCompliantMBeanException {
        if (info != null) {
            synchronized (mbeanInfoCache) {
                if (mbeanInfoCache.get(c) == null) {
                    mbeanInfoCache.put(c, info);
                }
            }
        }
        if (mbeanInterface != null) {
            synchronized (mbeanInterfaceCache) {
                if ((mbeanInterfaceCache.get(c) == null) || (((WeakReference)(WeakReference)mbeanInterfaceCache.get(c)).get() == null)) {
                    mbeanInterfaceCache.put(c, new WeakReference(mbeanInterface));
                }
            }
        }
    }
    
    Class getCachedMBeanInterface(Class c) {
        synchronized (mbeanInterfaceCache) {
            return (Class)((Class)((WeakReference)(WeakReference)mbeanInterfaceCache.get(c)).get());
        }
    }
    
    MBeanInfo getCachedMBeanInfo(Class c) {
        synchronized (mbeanInfoCache) {
            return (MBeanInfo)(MBeanInfo)mbeanInfoCache.get(c);
        }
    }
    
    Class findClass(String className, ClassLoader loader) throws ReflectionException {
        return MBeanInstantiatorImpl.loadClass(className, loader);
    }
    
    Class[] findSignatureClasses(String[] signature, ClassLoader loader) throws ReflectionException {
        return ((signature == null) ? null : MBeanInstantiatorImpl.loadSignatureClasses(signature, loader));
    }
    
    Object getAttribute(Object instance, String attribute, Class mbeanClass) throws MBeanException, AttributeNotFoundException, ReflectionException {
        if (attribute == null) {
            final RuntimeException r = new IllegalArgumentException("Attribute name cannot be null");
            throw new RuntimeOperationsException(r, "Exception occured trying to invoke the getter on the MBean");
        }
        Method meth = null;
        meth = findGetter(mbeanClass, attribute);
        if (meth == null) {
            if (isTraceOn()) {
                trace("getAttribute", "Cannot find getter for " + attribute + " in class " + mbeanClass.getName());
            }
            throw new AttributeNotFoundException(attribute + " not accessible");
        }
        if (isTraceOn()) {
            trace("getAttribute", "Invoke callback");
        }
        Object result = null;
        try {
            result = meth.invoke(instance, (Object[])null);
        } catch (InvocationTargetException e) {
            Throwable t = e.getTargetException();
            if (t instanceof RuntimeException) {
                debugX("getAttribute", t);
                final String msg = "RuntimeException thrown in the getter for the attribute " + attribute;
                throw wrapRuntimeException((RuntimeException)(RuntimeException)t, msg);
            } else if (t instanceof Error) {
                debugX("getAttribute", t);
                throw new RuntimeErrorException((Error)(Error)t, "Error thrown in the getter for the attribute " + attribute);
            } else {
                debugX("getAttribute", t);
                throw new MBeanException((Exception)(Exception)t, "Exception thrown in the getter for the attribute " + attribute);
            }
        } catch (RuntimeException e) {
            debugX("getAttribute", e);
            throw new RuntimeOperationsException(e, "RuntimeException thrown trying to invoke the getter" + " for the attribute " + attribute);
        } catch (IllegalAccessException e) {
            debugX("getAttribute", e);
            throw new ReflectionException(e, "Exception thrown trying to" + " invoke the getter for the attribute " + attribute);
        } catch (Error e) {
            debugX("getAttribute", e);
            throw new RuntimeErrorException((Error)e, "Error thrown trying to invoke the getter " + " for the attribute " + attribute);
        }
        if (isTraceOn()) {
            trace("getAttribute", attribute + "= " + result + "\n");
        }
        return result;
    }
    
    Object setAttribute(Object instance, Attribute attribute, Class mbeanClass) throws AttributeNotFoundException, InvalidAttributeValueException, MBeanException, ReflectionException {
        if (attribute == null) {
            final RuntimeException r = new IllegalArgumentException("Attribute name cannot be null");
            throw new RuntimeOperationsException(r, "Exception occured trying to invoke the setter on the MBean");
        }
        final Class objClass = instance.getClass();
        final ClassLoader aLoader = objClass.getClassLoader();
        Object result = null;
        final Object value = attribute.getValue();
        final String attname = attribute.getName();
        Method meth = null;
        if (value == null) {
            meth = findSetter(mbeanClass, attname);
        } else {
            meth = findSetter(mbeanClass, attname, value.getClass());
        }
        if (meth == null) {
            Class primClass = findPrimForClass(value);
            if (primClass != null) {
                meth = findSetter(mbeanClass, attname, primClass);
            }
        }
        if (meth == null) {
            meth = findSetter(mbeanClass, attname);
            if (meth == null) {
                if (isTraceOn()) {
                    trace("setAttribute", "Cannot find setter for " + attribute + " in class " + mbeanClass.getName());
                }
                throw new AttributeNotFoundException(attname + " not accessible");
            } else {
                final Object v = attribute.getValue();
                if (v == null) {
                    throw new InvalidAttributeValueException("attribute= " + attname + " value = null");
                } else {
                    throw new InvalidAttributeValueException("attribute= " + attname + " value = " + v);
                }
            }
        }
        if (isTraceOn()) {
            trace("setAttribute", "Invoking the set method for " + attname);
        }
        final Object[] values = new Object[1];
        values[0] = value;
        try {
            result = meth.invoke(instance, values);
        } catch (IllegalAccessException e) {
            debugX("setAttribute", e);
            throw new ReflectionException(e, "IllegalAccessException occured trying to invoke the setter on the MBean");
        } catch (InvocationTargetException e) {
            Throwable t = e.getTargetException();
            debugX("setAttribute", t);
            if (t instanceof RuntimeException) {
                final String msg = "RuntimeException thrown in the setter for the attribute " + attribute;
                throw wrapRuntimeException((RuntimeException)(RuntimeException)t, msg);
            } else if (t instanceof Error) {
                throw new RuntimeErrorException((Error)(Error)t, "Error thrown in the MBean\'s setter");
            } else {
                throw new MBeanException((Exception)(Exception)t, "Exception thrown in the MBean\'s setter");
            }
        }
        if (isTraceOn()) {
            trace("setAttribute", attname + "= " + value);
        }
        return value;
    }
    
    MBeanNotificationInfo[] findNotifications(Object moi) {
        if (moi instanceof javax.management.NotificationBroadcaster) {
            MBeanNotificationInfo[] mbn = ((NotificationBroadcaster)(NotificationBroadcaster)moi).getNotificationInfo();
            if (mbn == null) {
                return new MBeanNotificationInfo[0];
            }
            MBeanNotificationInfo[] result = new MBeanNotificationInfo[mbn.length];
            for (int i = 0; i < mbn.length; i++) {
                result[i] = (MBeanNotificationInfo)(MBeanNotificationInfo)mbn[i].clone();
            }
            return result;
        }
        return new MBeanNotificationInfo[0];
    }
    
    public static Method findMethod(Class classObj, String name, Class[] parameterTypes) {
        Method method = null;
        try {
            method = classObj.getMethod(name, parameterTypes);
        } catch (Exception e) {
        }
        return method;
    }
    
    public static Method findMethod(Class classObj, String name) {
        Method method = null;
        try {
            Method[] methods = classObj.getMethods();
            int i = 0;
            while ((i < methods.length) && !methods[i].getName().equals(name)) {
                i++;
            }
            if (i < methods.length) {
                method = methods[i];
            }
        } catch (Exception e) {
        }
        return method;
    }
    
    public static Method findMethod(Class classObj, String name, int paramCount) {
        Method method = null;
        try {
            Method[] methods = classObj.getMethods();
            int i = 0;
            boolean found = false;
            while ((i < methods.length) && !found) {
                found = methods[i].getName().equals(name);
                if (found) {
                    found = (methods[i].getParameterTypes().length == paramCount);
                }
                i++;
            }
            if (found) {
                method = methods[i - 1];
            }
        } catch (Exception e) {
        }
        return method;
    }
    
    public static Method findGetter(Class classObj, String attribute) {
        if (attribute.length() == 0) return null;
        Method m = findMethod(classObj, "get" + attribute, null);
        if (m != null && m.getReturnType() != Void.TYPE) return m;
        m = findMethod(classObj, "is" + attribute, null);
        if (m != null && m.getReturnType() == Boolean.TYPE) return m;
        return null;
    }
    
    public static Method findSetter(Class classObj, String attribute, Class type) {
        Method mth = findMethod(classObj, "set" + attribute, 1);
        if (mth != null) {
            Class[] pars = mth.getParameterTypes();
            if (pars[0].isAssignableFrom(type)) {
                return mth;
            }
        }
        return null;
    }
    
    public static Method findSetter(Class classObj, String attribute) {
        return findMethod(classObj, "set" + attribute, 1);
    }
    
    public static Constructor findConstructor(Class theClass, Class[] parameterTypes) {
        Constructor mth = null;
        try {
            mth = theClass.getConstructor(parameterTypes);
        } catch (Exception e) {
            return null;
        }
        return mth;
    }
    
    public static Class findClassForPrim(String primName) {
        return (Class)(Class)primitiveClasses.get(primName);
    }
    
    public static Class findPrimForClass(Object value) {
        if (value instanceof Boolean) return Boolean.TYPE; else if (value instanceof Character) return Character.TYPE; else if (value instanceof Byte) return Byte.TYPE; else if (value instanceof Short) return Short.TYPE; else if (value instanceof Integer) return Integer.TYPE; else if (value instanceof Long) return Long.TYPE; else if (value instanceof Float) return Float.TYPE; else if (value instanceof Double) return Double.TYPE;
        return null;
    }
    
    static String[] findSignatures(Class[] clz) {
        String[] signers = new String[clz.length];
        for (int i = 0; i < clz.length; i++) {
            signers[i] = findSignature(clz[i]);
        }
        return signers;
    }
    
    static String findSignature(Class clz) {
        return clz.getName();
    }
    
    private RuntimeException wrapRuntimeException(RuntimeException re, String msg) {
        if (wrapRuntimeExceptions) return new RuntimeMBeanException(re, msg); else return re;
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
