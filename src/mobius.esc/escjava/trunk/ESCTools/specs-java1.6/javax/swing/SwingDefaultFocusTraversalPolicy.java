package javax.swing;

import java.awt.Component;
import java.io.*;

class SwingDefaultFocusTraversalPolicy extends java.awt.DefaultFocusTraversalPolicy {
    
    SwingDefaultFocusTraversalPolicy() {
        
    }
    
    public boolean accept(Component aComponent) {
        return super.accept(aComponent);
    }
}
