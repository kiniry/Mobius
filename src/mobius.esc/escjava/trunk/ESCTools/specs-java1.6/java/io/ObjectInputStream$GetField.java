package java.io;

public abstract class ObjectInputStream$GetField {
    
    public ObjectInputStream$GetField() {
        
    }
    
    public abstract ObjectStreamClass getObjectStreamClass();
    
    public abstract boolean defaulted(String name) throws IOException;
    
    public abstract boolean get(String name, boolean val) throws IOException;
    
    public abstract byte get(String name, byte val) throws IOException;
    
    public abstract char get(String name, char val) throws IOException;
    
    public abstract short get(String name, short val) throws IOException;
    
    public abstract int get(String name, int val) throws IOException;
    
    public abstract long get(String name, long val) throws IOException;
    
    public abstract float get(String name, float val) throws IOException;
    
    public abstract double get(String name, double val) throws IOException;
    
    public abstract Object get(String name, Object val) throws IOException;
}
