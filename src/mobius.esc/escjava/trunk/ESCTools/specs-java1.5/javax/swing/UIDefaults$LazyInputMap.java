package javax.swing;

import javax.swing.border.*;
import java.lang.reflect.*;

public class UIDefaults$LazyInputMap implements UIDefaults$LazyValue {
    private Object[] bindings;
    
    public UIDefaults$LazyInputMap(Object[] bindings) {
        
        this.bindings = bindings;
    }
    
    public Object createValue(UIDefaults table) {
        if (bindings != null) {
            InputMap km = LookAndFeel.makeInputMap(bindings);
            return km;
        }
        return null;
    }
}
