package javax.swing;

import java.util.*;

public abstract class InputVerifier {
    
    public InputVerifier() {
        
    }
    
    public abstract boolean verify(JComponent input);
    
    public boolean shouldYieldFocus(JComponent input) {
        return verify(input);
    }
}
