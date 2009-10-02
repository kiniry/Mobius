package com.sun.jmx.mbeanserver;

import javax.management.ObjectName;

class ClassLoaderRepositorySupport$LoaderEntry {
    ObjectName name;
    ClassLoader loader;
    
    ClassLoaderRepositorySupport$LoaderEntry(ObjectName name, ClassLoader loader) {
        
        this.name = name;
        this.loader = loader;
    }
}
