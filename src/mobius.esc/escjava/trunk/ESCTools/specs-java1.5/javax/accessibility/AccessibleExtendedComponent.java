package javax.accessibility;

public interface AccessibleExtendedComponent extends AccessibleComponent {
    
    public String getToolTipText();
    
    public String getTitledBorderText();
    
    public AccessibleKeyBinding getAccessibleKeyBinding();
}
