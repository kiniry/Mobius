package com.sun.jmx.mbeanserver;

import java.io.ObjectInputStream;
import java.io.InputStream;
import java.io.IOException;
import java.io.ObjectStreamClass;
import javax.management.*;

class ObjectInputStreamWithLoader extends ObjectInputStream {
    private ClassLoader loader;
    
    public ObjectInputStreamWithLoader(InputStream in, ClassLoader theLoader) throws IOException {
        super(in);
        this.loader = theLoader;
    }
    
    protected Class resolveClass(ObjectStreamClass aClass) throws IOException, ClassNotFoundException {
        if (loader == null) {
            return super.resolveClass(aClass);
        } else {
            String name = aClass.getName();
            return Class.forName(name, false, loader);
        }
    }
}
