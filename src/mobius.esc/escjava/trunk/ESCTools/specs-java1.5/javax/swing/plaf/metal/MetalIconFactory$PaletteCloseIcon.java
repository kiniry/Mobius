package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

public class MetalIconFactory$PaletteCloseIcon implements Icon, UIResource, Serializable {
    
    public MetalIconFactory$PaletteCloseIcon() {
        
    }
    int iconSize = 7;
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        JButton parentButton = (JButton)(JButton)c;
        ButtonModel buttonModel = parentButton.getModel();
        Color back;
        Color highlight = MetalLookAndFeel.getPrimaryControlHighlight();
        Color shadow = MetalLookAndFeel.getPrimaryControlInfo();
        if (buttonModel.isPressed() && buttonModel.isArmed()) {
            back = shadow;
        } else {
            back = MetalLookAndFeel.getPrimaryControlDarkShadow();
        }
        g.translate(x, y);
        g.setColor(back);
        g.drawLine(0, 1, 5, 6);
        g.drawLine(1, 0, 6, 5);
        g.drawLine(1, 1, 6, 6);
        g.drawLine(6, 1, 1, 6);
        g.drawLine(5, 0, 0, 5);
        g.drawLine(5, 1, 1, 5);
        g.setColor(highlight);
        g.drawLine(6, 2, 5, 3);
        g.drawLine(2, 6, 3, 5);
        g.drawLine(6, 6, 6, 6);
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return iconSize;
    }
    
    public int getIconHeight() {
        return iconSize;
    }
}
