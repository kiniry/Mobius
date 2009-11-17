package com.sun.jmx.mbeanserver;

import java.io.PrintWriter;
import java.io.StringWriter;
import javax.management.*;
import com.sun.jmx.trace.Trace;

abstract class BaseMetaDataImpl implements MetaData {
    private static final String dbgTag = "BaseMetaDataImpl";
    
    BaseMetaDataImpl() {
        
    }
    
    public abstract MBeanInfo getMBeanInfo(Object moi) throws IntrospectionException;
    
    public abstract Object getAttribute(Object instance, String attribute) throws MBeanException, AttributeNotFoundException, ReflectionException;
    
    public abstract AttributeList getAttributes(Object instance, String[] attributes) throws ReflectionException;
    
    public abstract AttributeList setAttributes(Object instance, AttributeList attributes) throws ReflectionException;
    
    public abstract Object setAttribute(Object instance, Attribute attribute) throws AttributeNotFoundException, InvalidAttributeValueException, MBeanException, ReflectionException;
    
    public abstract Object invoke(Object instance, String operationName, Object[] params, String[] signature) throws MBeanException, ReflectionException;
    
    public ObjectName preRegisterInvoker(Object moi, ObjectName name, MBeanServer mbs) throws InstanceAlreadyExistsException, MBeanRegistrationException {
        if (!(moi instanceof MBeanRegistration)) return name;
        final ObjectName newName;
        try {
            newName = (ObjectName)((MBeanRegistration)(MBeanRegistration)moi).preRegister(mbs, name);
        } catch (RuntimeException e) {
            throw new RuntimeMBeanException((RuntimeException)e, "RuntimeException thrown in preRegister method");
        } catch (Error er) {
            throw new RuntimeErrorException((Error)er, "Error thrown in preRegister method");
        } catch (MBeanRegistrationException r) {
            throw (MBeanRegistrationException)r;
        } catch (Exception ex) {
            throw new MBeanRegistrationException((Exception)ex, "Exception thrown in preRegister method");
        }
        if (newName != null) return newName; else return name;
    }
    
    public void postRegisterInvoker(Object moi, boolean registrationDone) {
        if (!(moi instanceof MBeanRegistration)) return;
        try {
            ((MBeanRegistration)(MBeanRegistration)moi).postRegister(new Boolean(registrationDone));
        } catch (RuntimeException e) {
            throw new RuntimeMBeanException((RuntimeException)e, "RuntimeException thrown in postRegister method");
        } catch (Error er) {
            throw new RuntimeErrorException((Error)er, "Error thrown in postRegister method");
        }
    }
    
    public void preDeregisterInvoker(Object moi) throws MBeanRegistrationException {
        if (!(moi instanceof MBeanRegistration)) return;
        try {
            ((MBeanRegistration)(MBeanRegistration)moi).preDeregister();
        } catch (RuntimeException e) {
            throw new RuntimeMBeanException((RuntimeException)e, "RuntimeException thrown in preDeregister method");
        } catch (Error er) {
            throw new RuntimeErrorException((Error)er, "Error thrown in preDeregister method");
        } catch (MBeanRegistrationException t) {
            throw (MBeanRegistrationException)t;
        } catch (Exception ex) {
            throw new MBeanRegistrationException((Exception)ex, "Exception thrown in preDeregister method");
        }
    }
    
    public void postDeregisterInvoker(Object moi) {
        if (!(moi instanceof MBeanRegistration)) return;
        try {
            ((MBeanRegistration)(MBeanRegistration)moi).postDeregister();
        } catch (RuntimeException e) {
            throw new RuntimeMBeanException((RuntimeException)e, "RuntimeException thrown in postDeregister method");
        } catch (Error er) {
            throw new RuntimeErrorException((Error)er, "Error thrown in postDeregister method");
        }
    }
    
    public String getMBeanClassName(Object moi) throws IntrospectionException, NotCompliantMBeanException {
        final MBeanInfo mbi;
        try {
            mbi = getMBeanInfo(moi);
        } catch (SecurityException x) {
            throw x;
        } catch (IntrospectionException x) {
            throw x;
        } catch (Exception x) {
            throw new NotCompliantMBeanException("Can\'t obtain MBeanInfo " + "from DynamicMBean: " + x);
        }
        if (mbi == null) {
            throw new NotCompliantMBeanException("The MBeanInfo returned is null");
        }
        final String className = mbi.getClassName();
        if (className == null) {
            throw new IntrospectionException("The class Name returned is null");
        }
        return className;
    }
    
    public boolean isInstanceOf(Object instance, String className) throws ReflectionException {
        try {
            final String cn = getMBeanClassName(instance);
            if (cn.equals(className)) return true;
            try {
                final ClassLoader cl = instance.getClass().getClassLoader();
                final Class classNameClass = findClass(className, cl);
                if (classNameClass == null) return false;
                if (classNameClass.isInstance(instance)) return true;
                final Class instanceClass = findClass(cn, cl);
                if (instanceClass == null) return false;
                return classNameClass.isAssignableFrom(instanceClass);
            } catch (Exception x) {
                debugX("isInstanceOf", x);
                return false;
            }
        } catch (IntrospectionException x) {
            debugX("isInstanceOf", x);
            throw new ReflectionException(x, x.getMessage());
        } catch (NotCompliantMBeanException x) {
            debugX("isInstanceOf", x);
            throw new ReflectionException(x, x.getMessage());
        }
    }
    
    Class findClass(String className, ClassLoader loader) throws ReflectionException {
        try {
            if (loader == null) return Class.forName(className); else return loader.loadClass(className);
        } catch (ClassNotFoundException x) {
            throw new ReflectionException(x, x.getMessage());
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
