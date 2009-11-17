package com.sun.jmx.mbeanserver;

import javax.management.ObjectName;
import javax.management.loading.ClassLoaderRepository;

public interface ModifiableClassLoaderRepository extends ClassLoaderRepository {
    
    public void addClassLoader(ClassLoader loader);
    
    public void removeClassLoader(ClassLoader loader);
    
    public void addClassLoader(ObjectName name, ClassLoader loader);
    
    public void removeClassLoader(ObjectName name);
    
    public ClassLoader getClassLoader(ObjectName name);
}
