package javax.accessibility;

public interface AccessibleValue {
    
    public Number getCurrentAccessibleValue();
    
    public boolean setCurrentAccessibleValue(Number n);
    
    public Number getMinimumAccessibleValue();
    
    public Number getMaximumAccessibleValue();
}
