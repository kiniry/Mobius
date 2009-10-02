package com.sun.jmx.mbeanserver;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.io.*;
import javax.management.*;
import com.sun.jmx.trace.Trace;
import sun.reflect.misc.ReflectUtil;

class MBeanInstantiatorImpl implements MBeanInstantiator {
    private final ModifiableClassLoaderRepository clr;
    private static final String dbgTag = "MBeanInstantiatorImpl";
    
    public MBeanInstantiatorImpl(ModifiableClassLoaderRepository clr) {
        
        this.clr = clr;
    }
    
    public void testCreation(Class c) throws NotCompliantMBeanException {
        Introspector.testCreation(c);
    }
    
    public Class findClassWithDefaultLoaderRepository(String className) throws ReflectionException {
        Class theClass;
        if (className == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("The class name cannot be null"), "Exception occured during object instantiation");
        }
        try {
            if (clr == null) throw new ClassNotFoundException(className);
            theClass = clr.loadClass(className);
        } catch (ClassNotFoundException ee) {
            throw new ReflectionException(ee, "The MBean class could not be loaded by the default loader repository");
        }
        return theClass;
    }
    
    public Class findClass(String className, ClassLoader loader) throws ReflectionException {
        return loadClass(className, loader);
    }
    
    public Class findClass(String className, ObjectName aLoader) throws ReflectionException, InstanceNotFoundException {
        Class theClass = null;
        if (aLoader == null) throw new RuntimeOperationsException(new IllegalArgumentException(), "Null loader passed in parameter");
        ClassLoader loader = null;
        synchronized (this) {
            if (clr != null) loader = clr.getClassLoader(aLoader);
        }
        if (loader == null) {
            throw new InstanceNotFoundException("The loader named " + aLoader + " is not registered in the MBeanServer");
        }
        return findClass(className, loader);
    }
    
    public Class[] findSignatureClasses(String[] signature, ClassLoader loader) throws ReflectionException {
        if (signature == null) return null;
        final ClassLoader aLoader = (ClassLoader)loader;
        final int length = signature.length;
        final Class[] tab = new Class[length];
        if (length == 0) return tab;
        try {
            for (int i = 0; i < length; i++) {
                final Class primCla = StandardMetaDataImpl.findClassForPrim(signature[i]);
                if (primCla != null) {
                    tab[i] = primCla;
                    continue;
                }
                if (aLoader != null) {
                    tab[i] = Class.forName(signature[i], false, aLoader);
                } else {
                    tab[i] = findClass(signature[i], this.getClass().getClassLoader());
                }
            }
        } catch (ClassNotFoundException e) {
            debugX("findSignatureClasses", e);
            throw new ReflectionException(e, "The parameter class could not be found");
        } catch (RuntimeException e) {
            debugX("findSignatureClasses", e);
            throw e;
        }
        return tab;
    }
    
    public Object instantiate(Class theClass) throws ReflectionException, MBeanException {
        Object moi = null;
        Constructor cons = StandardMetaDataImpl.findConstructor(theClass, null);
        if (cons == null) {
            throw new ReflectionException(new NoSuchMethodException("No such constructor"));
        }
        try {
            ReflectUtil.checkPackageAccess(theClass);
            moi = cons.newInstance((Object[])null);
        } catch (InvocationTargetException e) {
            Throwable t = e.getTargetException();
            if (t instanceof RuntimeException) {
                throw new RuntimeMBeanException((RuntimeException)(RuntimeException)t, "RuntimeException thrown in the MBean\'s empty constructor");
            } else if (t instanceof Error) {
                throw new RuntimeErrorException((Error)(Error)t, "Error thrown in the MBean\'s empty constructor");
            } else {
                throw new MBeanException((Exception)(Exception)t, "Exception thrown in the MBean\'s empty constructor");
            }
        } catch (NoSuchMethodError error) {
            throw new ReflectionException(new NoSuchMethodException("No constructor"), "No such constructor");
        } catch (InstantiationException e) {
            throw new ReflectionException(e, "Exception thrown trying to invoke the MBean\'s empty constructor");
        } catch (IllegalAccessException e) {
            throw new ReflectionException(e, "Exception thrown trying to invoke the MBean\'s empty constructor");
        } catch (IllegalArgumentException e) {
            throw new ReflectionException(e, "Exception thrown trying to invoke the MBean\'s empty constructor");
        }
        return moi;
    }
    
    public Object instantiate(Class theClass, Object[] params, String[] signature, ClassLoader loader) throws ReflectionException, MBeanException {
        final Class[] tab;
        Object moi = null;
        try {
            ClassLoader aLoader = (ClassLoader)theClass.getClassLoader();
            tab = ((signature == null) ? null : findSignatureClasses(signature, aLoader));
        } catch (IllegalArgumentException e) {
            throw new ReflectionException(e, "The constructor parameter classes could not be loaded");
        }
        Constructor cons = null;
        cons = StandardMetaDataImpl.findConstructor(theClass, tab);
        if (cons == null) {
            throw new ReflectionException(new NoSuchMethodException("No such constructor"));
        }
        try {
            ReflectUtil.checkPackageAccess(theClass);
            moi = cons.newInstance(params);
        } catch (NoSuchMethodError error) {
            throw new ReflectionException(new NoSuchMethodException("No such constructor found"), "No such constructor");
        } catch (InstantiationException e) {
            throw new ReflectionException(e, "Exception thrown trying to invoke the MBean\'s constructor");
        } catch (IllegalAccessException e) {
            throw new ReflectionException(e, "Exception thrown trying to invoke the MBean\'s constructor");
        } catch (InvocationTargetException e) {
            Throwable th = e.getTargetException();
            if (th instanceof RuntimeException) {
                throw new RuntimeMBeanException((RuntimeException)(RuntimeException)th, "RuntimeException thrown in the MBean\'s constructor");
            } else if (th instanceof Error) {
                throw new RuntimeErrorException((Error)(Error)th, "Error thrown in the MBean\'s constructor");
            } else {
                throw new MBeanException((Exception)(Exception)th, "Exception thrown in the MBean\'s constructor");
            }
        }
        return moi;
    }
    
    public ObjectInputStream deserialize(ClassLoader loader, byte[] data) throws OperationsException {
        if (data == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException(), "Null data passed in parameter");
        }
        if (data.length == 0) {
            throw new RuntimeOperationsException(new IllegalArgumentException(), "Empty data passed in parameter");
        }
        ByteArrayInputStream bIn;
        ObjectInputStream objIn;
        String typeStr;
        bIn = new ByteArrayInputStream(data);
        try {
            objIn = new ObjectInputStreamWithLoader(bIn, loader);
        } catch (IOException e) {
            throw new OperationsException("An IOException occured trying to de-serialize the data");
        }
        return objIn;
    }
    
    public ObjectInputStream deserialize(String className, ObjectName loaderName, byte[] data, ClassLoader loader) throws InstanceNotFoundException, OperationsException, ReflectionException {
        if (data == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException(), "Null data passed in parameter");
        }
        if (data.length == 0) {
            throw new RuntimeOperationsException(new IllegalArgumentException(), "Empty data passed in parameter");
        }
        if (className == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException(), "Null className passed in parameter");
        }
        Class theClass = null;
        if (loaderName == null) {
            theClass = findClass(className, loader);
        } else {
            try {
                ClassLoader instance = null;
                if (clr != null) instance = clr.getClassLoader(loaderName);
                if (instance == null) throw new ClassNotFoundException(className);
                theClass = Class.forName(className, false, instance);
            } catch (ClassNotFoundException e) {
                throw new ReflectionException(e, "The MBean class could not be loaded by the " + loaderName.toString() + " class loader");
            }
        }
        ByteArrayInputStream bIn;
        ObjectInputStream objIn;
        String typeStr;
        bIn = new ByteArrayInputStream(data);
        try {
            objIn = new ObjectInputStreamWithLoader(bIn, theClass.getClassLoader());
        } catch (IOException e) {
            throw new OperationsException("An IOException occured trying to de-serialize the data");
        }
        return objIn;
    }
    
    public Object instantiate(String className) throws ReflectionException, MBeanException {
        return instantiate(className, (Object[])null, (String[])null, null);
    }
    
    public Object instantiate(String className, ObjectName loaderName, ClassLoader loader) throws ReflectionException, MBeanException, InstanceNotFoundException {
        return instantiate(className, loaderName, (Object[])null, (String[])null, loader);
    }
    
    public Object instantiate(String className, Object[] params, String[] signature, ClassLoader loader) throws ReflectionException, MBeanException {
        Class theClass = findClassWithDefaultLoaderRepository(className);
        return instantiate(theClass, params, signature, loader);
    }
    
    public Object instantiate(String className, ObjectName loaderName, Object[] params, String[] signature, ClassLoader loader) throws ReflectionException, MBeanException, InstanceNotFoundException {
        Class theClass;
        if (loaderName == null) {
            theClass = findClass(className, loader);
        } else {
            theClass = findClass(className, loaderName);
        }
        return instantiate(theClass, params, signature, loader);
    }
    
    public ModifiableClassLoaderRepository getClassLoaderRepository() {
        return clr;
    }
    
    static Class loadClass(String className, ClassLoader loader) throws ReflectionException {
        Class theClass = null;
        if (className == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("The class name cannot be null"), "Exception occured during object instantiation");
        }
        try {
            if (loader == null) loader = MBeanInstantiatorImpl.class.getClassLoader();
            if (loader != null) {
                theClass = Class.forName(className, false, loader);
            } else {
                theClass = Class.forName(className);
            }
        } catch (ClassNotFoundException e) {
            throw new ReflectionException(e, "The MBean class could not be loaded by the context classloader");
        }
        return theClass;
    }
    
    static Class[] loadSignatureClasses(String[] signature, ClassLoader loader) throws ReflectionException {
        if (signature == null) return null;
        final ClassLoader aLoader = (loader == null ? MBeanInstantiatorImpl.class.getClassLoader() : loader);
        final int length = signature.length;
        final Class[] tab = new Class[length];
        if (length == 0) return tab;
        try {
            for (int i = 0; i < length; i++) {
                final Class primCla = StandardMetaDataImpl.findClassForPrim(signature[i]);
                if (primCla != null) {
                    tab[i] = primCla;
                    continue;
                }
                tab[i] = Class.forName(signature[i], false, aLoader);
            }
        } catch (ClassNotFoundException e) {
            debugX("findSignatureClasses", e);
            throw new ReflectionException(e, "The parameter class could not be found");
        } catch (RuntimeException e) {
            debugX("findSignatureClasses", e);
            throw e;
        }
        return tab;
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
