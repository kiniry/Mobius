package javax.swing.plaf.metal;

import java.awt.*;
import java.util.*;
import javax.swing.*;
import javax.swing.plaf.*;

class OceanTheme$IFIcon extends IconUIResource {
    private Icon pressed;
    
    public OceanTheme$IFIcon(Icon normal, Icon pressed) {
        super(normal);
        this.pressed = pressed;
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        ButtonModel model = ((AbstractButton)(AbstractButton)c).getModel();
        if (model.isPressed() && model.isArmed()) {
            pressed.paintIcon(c, g, x, y);
        } else {
            super.paintIcon(c, g, x, y);
        }
    }
}
