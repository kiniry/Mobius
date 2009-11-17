package com.sun.jmx.mbeanserver;

import javax.management.*;
import java.io.ObjectInputStream;

public interface MBeanInstantiator {
    
    public void testCreation(Class c) throws NotCompliantMBeanException;
    
    public Class findClassWithDefaultLoaderRepository(String className) throws ReflectionException;
    
    public ModifiableClassLoaderRepository getClassLoaderRepository();
    
    public Class findClass(String className, ClassLoader loader) throws ReflectionException;
    
    public Class findClass(String className, ObjectName loaderName) throws ReflectionException, InstanceNotFoundException;
    
    public Class[] findSignatureClasses(String[] signature, ClassLoader loader) throws ReflectionException;
    
    public ObjectInputStream deserialize(ClassLoader loader, byte[] data) throws OperationsException;
    
    public ObjectInputStream deserialize(String className, ObjectName loaderName, byte[] data, ClassLoader loader) throws InstanceNotFoundException, OperationsException, ReflectionException;
    
    public Object instantiate(String className) throws ReflectionException, MBeanException;
    
    public Object instantiate(String className, ObjectName loaderName, ClassLoader loader) throws ReflectionException, MBeanException, InstanceNotFoundException;
    
    public Object instantiate(String className, Object[] params, String[] signature, ClassLoader loader) throws ReflectionException, MBeanException;
    
    public Object instantiate(String className, ObjectName loaderName, Object[] params, String[] signature, ClassLoader loader) throws ReflectionException, MBeanException, InstanceNotFoundException;
    
    public Object instantiate(Class theClass) throws ReflectionException, MBeanException;
    
    public Object instantiate(Class theClass, Object[] params, String[] signature, ClassLoader loader) throws ReflectionException, MBeanException;
}
