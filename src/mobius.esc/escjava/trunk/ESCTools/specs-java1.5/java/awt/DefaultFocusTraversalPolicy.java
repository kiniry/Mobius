package java.awt;

import java.awt.peer.ComponentPeer;

public class DefaultFocusTraversalPolicy extends ContainerOrderFocusTraversalPolicy {
    
    public DefaultFocusTraversalPolicy() {
        
    }
    
    protected boolean accept(Component aComponent) {
        if (!(aComponent.isVisible() && aComponent.isDisplayable() && aComponent.isEnabled())) {
            return false;
        }
        if (!(aComponent instanceof Window)) {
            for (Container enableTest = aComponent.getParent(); enableTest != null; enableTest = enableTest.getParent()) {
                if (!(enableTest.isEnabled() || enableTest.isLightweight())) {
                    return false;
                }
                if (enableTest instanceof Window) {
                    break;
                }
            }
        }
        boolean focusable = aComponent.isFocusable();
        if (aComponent.isFocusTraversableOverridden()) {
            return focusable;
        }
        ComponentPeer peer = aComponent.getPeer();
        return (peer != null && peer.isFocusable());
    }
}
