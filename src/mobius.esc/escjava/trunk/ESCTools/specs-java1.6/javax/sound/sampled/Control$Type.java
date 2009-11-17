package javax.sound.sampled;

public class Control$Type {
    private String name;
    
    protected Control$Type(String name) {
        
        this.name = name;
    }
    
    public final boolean equals(Object obj) {
        return super.equals(obj);
    }
    
    public final int hashCode() {
        return super.hashCode();
    }
    
    public final String toString() {
        return name;
    }
}
