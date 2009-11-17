package javax.swing;

import java.awt.Component;
import java.awt.Container;

public interface RootPaneContainer {
    
    JRootPane getRootPane();
    
    void setContentPane(Container contentPane);
    
    Container getContentPane();
    
    void setLayeredPane(JLayeredPane layeredPane);
    
    JLayeredPane getLayeredPane();
    
    void setGlassPane(Component glassPane);
    
    Component getGlassPane();
}
