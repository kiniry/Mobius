package javax.swing.text;

public abstract class NavigationFilter$FilterBypass {
    
    public NavigationFilter$FilterBypass() {
        
    }
    
    public abstract Caret getCaret();
    
    public abstract void setDot(int dot, Position$Bias bias);
    
    public abstract void moveDot(int dot, Position$Bias bias);
}
