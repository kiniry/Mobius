package javax.accessibility;

public interface AccessibleAction {
    public static final String TOGGLE_EXPAND = new String("toggle expand");
    public static final String INCREMENT = new String("increment");
    public static final String DECREMENT = new String("decrement");
    
    public int getAccessibleActionCount();
    
    public String getAccessibleActionDescription(int i);
    
    public boolean doAccessibleAction(int i);
}
