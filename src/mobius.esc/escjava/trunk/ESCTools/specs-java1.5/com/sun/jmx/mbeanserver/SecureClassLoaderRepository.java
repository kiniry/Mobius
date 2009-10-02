package com.sun.jmx.mbeanserver;

import javax.management.loading.ClassLoaderRepository;

final class SecureClassLoaderRepository implements ClassLoaderRepository {
    private final ClassLoaderRepository clr;
    
    public SecureClassLoaderRepository(ClassLoaderRepository clr) {
        
        this.clr = clr;
    }
    
    public final Class loadClass(String className) throws ClassNotFoundException {
        return clr.loadClass(className);
    }
    
    public final Class loadClassWithout(ClassLoader loader, String className) throws ClassNotFoundException {
        return clr.loadClassWithout(loader, className);
    }
    
    public final Class loadClassBefore(ClassLoader loader, String className) throws ClassNotFoundException {
        return clr.loadClassBefore(loader, className);
    }
}
