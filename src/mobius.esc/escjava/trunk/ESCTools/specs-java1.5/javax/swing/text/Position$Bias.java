package javax.swing.text;

public final class Position$Bias {
    public static final Position$Bias Forward = new Position$Bias("Forward");
    public static final Position$Bias Backward = new Position$Bias("Backward");
    
    public String toString() {
        return name;
    }
    
    private Position$Bias(String name) {
        
        this.name = name;
    }
    private String name;
}
