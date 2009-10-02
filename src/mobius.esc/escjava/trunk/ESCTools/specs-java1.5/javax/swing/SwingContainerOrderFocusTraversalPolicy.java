package javax.swing;

import java.awt.Component;
import java.util.*;
import java.util.logging.*;

class SwingContainerOrderFocusTraversalPolicy extends java.awt.ContainerOrderFocusTraversalPolicy {
    
    SwingContainerOrderFocusTraversalPolicy() {
        
    }
    
    public boolean accept(Component aComponent) {
        return super.accept(aComponent);
    }
}
