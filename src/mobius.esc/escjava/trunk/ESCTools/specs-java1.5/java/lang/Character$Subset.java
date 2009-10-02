package java.lang;

public class Character$Subset {
    private String name;
    
    protected Character$Subset(String name) {
        
        if (name == null) {
            throw new NullPointerException("name");
        }
        this.name = name;
    }
    
    public final boolean equals(Object obj) {
        return (this == obj);
    }
    
    public final int hashCode() {
        return super.hashCode();
    }
    
    public final String toString() {
        return name;
    }
}
