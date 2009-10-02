package java.io;

public abstract class ObjectOutputStream$PutField {
    
    public ObjectOutputStream$PutField() {
        
    }
    
    public abstract void put(String name, boolean val);
    
    public abstract void put(String name, byte val);
    
    public abstract void put(String name, char val);
    
    public abstract void put(String name, short val);
    
    public abstract void put(String name, int val);
    
    public abstract void put(String name, long val);
    
    public abstract void put(String name, float val);
    
    public abstract void put(String name, double val);
    
    public abstract void put(String name, Object val);
    
    
    public abstract void write(ObjectOutput out) throws IOException;
}
