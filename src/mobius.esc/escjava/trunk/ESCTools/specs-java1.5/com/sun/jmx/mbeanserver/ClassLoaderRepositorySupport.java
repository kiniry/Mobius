package com.sun.jmx.mbeanserver;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Hashtable;
import java.util.List;
import java.util.Vector;
import javax.management.ObjectName;
import javax.management.loading.PrivateClassLoader;
import com.sun.jmx.trace.Trace;

final class ClassLoaderRepositorySupport implements ModifiableClassLoaderRepository {
    
    ClassLoaderRepositorySupport() {
        
    }
    {
    }
    private static final ClassLoaderRepositorySupport$LoaderEntry[] EMPTY_LOADER_ARRAY = new ClassLoaderRepositorySupport$LoaderEntry[0];
    private ClassLoaderRepositorySupport$LoaderEntry[] loaders = EMPTY_LOADER_ARRAY;
    
    private synchronized boolean add(ObjectName name, ClassLoader cl) {
        List l = new ArrayList(Arrays.asList(loaders));
        l.add(new ClassLoaderRepositorySupport$LoaderEntry(name, cl));
        loaders = (ClassLoaderRepositorySupport$LoaderEntry[])(ClassLoaderRepositorySupport$LoaderEntry[])l.toArray(EMPTY_LOADER_ARRAY);
        return true;
    }
    
    private synchronized boolean remove(ObjectName name, ClassLoader cl) {
        final int size = loaders.length;
        for (int i = 0; i < size; i++) {
            ClassLoaderRepositorySupport$LoaderEntry entry = loaders[i];
            boolean match = (name == null) ? cl == entry.loader : name.equals(entry.name);
            if (match) {
                ClassLoaderRepositorySupport$LoaderEntry[] newloaders = new ClassLoaderRepositorySupport$LoaderEntry[size - 1];
                System.arraycopy(loaders, 0, newloaders, 0, i);
                System.arraycopy(loaders, i + 1, newloaders, i, size - 1 - i);
                loaders = newloaders;
                return true;
            }
        }
        return false;
    }
    private final Hashtable search = new Hashtable(10);
    private final Hashtable loadersWithNames = new Hashtable(10);
    private static final String dbgTag = "ClassLoaderRepositorySupport";
    
    public final Class loadClass(String className) throws ClassNotFoundException {
        return loadClass(loaders, className, null, null);
    }
    
    public final Class loadClassWithout(ClassLoader without, String className) throws ClassNotFoundException {
        if (isTraceOn()) {
            trace("loadClassWithout", className + "\twithout " + without);
        }
        if (without == null) return loadClass(loaders, className, null, null);
        startValidSearch(without, className);
        try {
            return loadClass(loaders, className, without, null);
        } finally {
            stopValidSearch(without, className);
        }
    }
    
    public final Class loadClassBefore(ClassLoader stop, String className) throws ClassNotFoundException {
        if (isTraceOn()) trace("loadClassBefore", className + "\tbefore " + stop);
        if (stop == null) return loadClass(loaders, className, null, null);
        startValidSearch(stop, className);
        try {
            return loadClass(loaders, className, null, stop);
        } finally {
            stopValidSearch(stop, className);
        }
    }
    
    private Class loadClass(final ClassLoaderRepositorySupport$LoaderEntry[] list, final String className, final ClassLoader without, final ClassLoader stop) throws ClassNotFoundException {
        final int size = list.length;
        for (int i = 0; i < size; i++) {
            try {
                final ClassLoader cl = list[i].loader;
                if (cl == null) return Class.forName(className, false, null);
                if (cl == without) continue;
                if (cl == stop) break;
                if (isTraceOn()) {
                    trace("loadClass", "trying loader = " + cl);
                }
                return Class.forName(className, false, cl);
            } catch (ClassNotFoundException e) {
            }
        }
        throw new ClassNotFoundException(className);
    }
    
    private synchronized void startValidSearch(ClassLoader aloader, String className) throws ClassNotFoundException {
        Vector excluded = (Vector)(Vector)search.get(className);
        if ((excluded != null) && (excluded.contains(aloader))) {
            if (isTraceOn()) {
                trace("startValidSearch", "already requested loader=" + aloader + " class= " + className);
            }
            throw new ClassNotFoundException(className);
        }
        if (excluded == null) {
            excluded = new Vector(1);
            search.put(className, excluded);
        }
        excluded.addElement(aloader);
        if (isTraceOn()) {
            trace("startValidSearch", "loader=" + aloader + " class= " + className);
        }
    }
    
    private synchronized void stopValidSearch(ClassLoader aloader, String className) {
        Vector excluded = (Vector)(Vector)search.get(className);
        if (excluded != null) {
            excluded.removeElement(aloader);
            if (isTraceOn()) {
                trace("stopValidSearch", "loader=" + aloader + " class= " + className);
            }
        }
    }
    
    public final void addClassLoader(ClassLoader loader) {
        add(null, loader);
    }
    
    public final void removeClassLoader(ClassLoader loader) {
        remove(null, loader);
    }
    
    public final synchronized void addClassLoader(ObjectName name, ClassLoader loader) {
        loadersWithNames.put(name, loader);
        if (!(loader instanceof PrivateClassLoader)) add(name, loader);
    }
    
    public final synchronized void removeClassLoader(ObjectName name) {
        ClassLoader loader = (ClassLoader)(ClassLoader)loadersWithNames.remove(name);
        if (!(loader instanceof PrivateClassLoader)) remove(name, loader);
    }
    
    public final ClassLoader getClassLoader(ObjectName name) {
        return (ClassLoader)(ClassLoader)loadersWithNames.get(name);
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
}
