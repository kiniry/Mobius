package java.lang.instrument;

public interface Instrumentation {
    
    void addTransformer(ClassFileTransformer transformer);
    
    boolean removeTransformer(ClassFileTransformer transformer);
    
    boolean isRedefineClassesSupported();
    
    void redefineClasses(ClassDefinition[] definitions) throws ClassNotFoundException, UnmodifiableClassException;
    
    Class[] getAllLoadedClasses();
    
    Class[] getInitiatedClasses(ClassLoader loader);
    
    long getObjectSize(Object objectToSize);
}
