package java.awt;

import java.beans.*;
import java.util.logging.*;
import java.lang.reflect.*;

final class KeyboardFocusManager$LightweightFocusRequest {
    final Component component;
    final boolean temporary;
    
    KeyboardFocusManager$LightweightFocusRequest(Component component, boolean temporary) {
        
        this.component = component;
        this.temporary = temporary;
    }
    
    public String toString() {
        return "LightweightFocusRequest[component=" + component + ",temporary=" + temporary + "]";
    }
}
