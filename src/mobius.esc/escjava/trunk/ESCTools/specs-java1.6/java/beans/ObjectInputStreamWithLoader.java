package java.beans;

import java.applet.*;
import java.awt.*;
import java.io.*;
import java.lang.reflect.Array;

class ObjectInputStreamWithLoader extends ObjectInputStream {
    private ClassLoader loader;
    
    public ObjectInputStreamWithLoader(InputStream in, ClassLoader loader) throws IOException, StreamCorruptedException {
        super(in);
        if (loader == null) {
            throw new IllegalArgumentException("Illegal null argument to ObjectInputStreamWithLoader");
        }
        this.loader = loader;
    }
    
    private Class primitiveType(char type) {
        switch (type) {
        case 'B': 
            return Byte.TYPE;
        
        case 'C': 
            return Character.TYPE;
        
        case 'D': 
            return Double.TYPE;
        
        case 'F': 
            return Float.TYPE;
        
        case 'I': 
            return Integer.TYPE;
        
        case 'J': 
            return Long.TYPE;
        
        case 'S': 
            return Short.TYPE;
        
        case 'Z': 
            return Boolean.TYPE;
        
        default: 
            return null;
        
        }
    }
    
    protected Class resolveClass(ObjectStreamClass classDesc) throws IOException, ClassNotFoundException {
        String cname = classDesc.getName();
        if (cname.startsWith("[")) {
            Class component;
            int dcount;
            for (dcount = 1; cname.charAt(dcount) == '['; dcount++) ;
            if (cname.charAt(dcount) == 'L') {
                component = loader.loadClass(cname.substring(dcount + 1, cname.length() - 1));
            } else {
                if (cname.length() != dcount + 1) {
                    throw new ClassNotFoundException(cname);
                }
                component = primitiveType(cname.charAt(dcount));
            }
            int[] dim = new int[dcount];
            for (int i = 0; i < dcount; i++) {
                dim[i] = 0;
            }
            return Array.newInstance(component, dim).getClass();
        } else {
            return loader.loadClass(cname);
        }
    }
}
