package javax.sound.sampled;

public abstract class Control {
    private final Control$Type type;
    
    protected Control(Control$Type type) {
        
        this.type = type;
    }
    
    public Control$Type getType() {
        return type;
    }
    
    public String toString() {
        return new String(getType() + " Control");
    }
    {
    }
}
