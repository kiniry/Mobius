package javax.swing;

import javax.swing.event.SwingPropertyChangeSupport;
import java.util.Properties;
import java.util.Vector;

class UIManager$LAFState {
    
    /*synthetic*/ UIManager$LAFState(javax.swing.UIManager$1 x0) {
        this();
    }
    
    private UIManager$LAFState() {
        
    }
    Properties swingProps;
    private UIDefaults[] tables = new UIDefaults[2];
    boolean initialized = false;
    MultiUIDefaults multiUIDefaults = new MultiUIDefaults(tables);
    LookAndFeel lookAndFeel;
    LookAndFeel multiLookAndFeel = null;
    Vector auxLookAndFeels = null;
    SwingPropertyChangeSupport changeSupport;
    
    UIDefaults getLookAndFeelDefaults() {
        return tables[0];
    }
    
    void setLookAndFeelDefaults(UIDefaults x) {
        tables[0] = x;
    }
    
    UIDefaults getSystemDefaults() {
        return tables[1];
    }
    
    void setSystemDefaults(UIDefaults x) {
        tables[1] = x;
    }
    
    public synchronized SwingPropertyChangeSupport getPropertyChangeSupport(boolean create) {
        if (create && changeSupport == null) {
            changeSupport = new SwingPropertyChangeSupport(UIManager.class);
        }
        return changeSupport;
    }
}
