package java.lang;

class ClassLoader$NativeLibrary {
    
    /*synthetic*/ static Class access$200(ClassLoader$NativeLibrary x0) {
        return x0.fromClass;
    }
    long handle;
    private int jniVersion;
    private Class fromClass;
    String name;
    
    native void load(String name);
    
    native long find(String name);
    
    native void unload();
    
    public ClassLoader$NativeLibrary(Class fromClass, String name) {
        
        this.name = name;
        this.fromClass = fromClass;
    }
    
    protected void finalize() {
        synchronized (ClassLoader.access$000()) {
            if (fromClass.getClassLoader() != null && handle != 0) {
                int size = ClassLoader.access$000().size();
                for (int i = 0; i < size; i++) {
                    if (name.equals(ClassLoader.access$000().elementAt(i))) {
                        ClassLoader.access$000().removeElementAt(i);
                        break;
                    }
                }
                ClassLoader.access$100().push(this);
                try {
                    unload();
                } finally {
                    ClassLoader.access$100().pop();
                }
            }
        }
    }
    
    static Class getFromClass() {
        return ((ClassLoader$NativeLibrary)((ClassLoader$NativeLibrary)ClassLoader.access$100().peek())).fromClass;
    }
}
