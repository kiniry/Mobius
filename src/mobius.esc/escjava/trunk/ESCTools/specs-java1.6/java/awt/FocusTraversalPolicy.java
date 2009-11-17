package java.awt;

public abstract class FocusTraversalPolicy {
    
    public FocusTraversalPolicy() {
        
    }
    
    public abstract Component getComponentAfter(Container aContainer, Component aComponent);
    
    public abstract Component getComponentBefore(Container aContainer, Component aComponent);
    
    public abstract Component getFirstComponent(Container aContainer);
    
    public abstract Component getLastComponent(Container aContainer);
    
    public abstract Component getDefaultComponent(Container aContainer);
    
    public Component getInitialComponent(Window window) {
        Component def = getDefaultComponent(window);
        if (def == null && window.isFocusableWindow()) {
            def = window;
        }
        return def;
    }
}
