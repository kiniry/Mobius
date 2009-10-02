package javax.swing;

import java.awt.*;
import sun.awt.ModalExclude;

class Popup$HeavyWeightWindow extends JWindow implements ModalExclude {
    
    Popup$HeavyWeightWindow(Window parent) {
        super(parent);
        setFocusableWindowState(false);
        setName("###overrideRedirect###");
    }
    
    public void update(Graphics g) {
        paint(g);
    }
    
    public void show() {
        this.pack();
        super.show();
    }
}
