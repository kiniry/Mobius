package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$RadioButtonIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ MetalIconFactory$RadioButtonIcon(javax.swing.plaf.metal.MetalIconFactory$1 x0) {
        this();
    }
    
    private MetalIconFactory$RadioButtonIcon() {
        
    }
    
    public void paintOceanIcon(Component c, Graphics g, int x, int y) {
        ButtonModel model = ((JRadioButton)(JRadioButton)c).getModel();
        boolean enabled = model.isEnabled();
        boolean pressed = (enabled && model.isPressed() && model.isArmed());
        boolean rollover = (enabled && model.isRollover());
        g.translate(x, y);
        if (enabled && !pressed) {
            MetalUtils.drawGradient(c, g, "RadioButton.gradient", 1, 1, 10, 10, true);
            g.setColor(c.getBackground());
            g.fillRect(1, 1, 1, 1);
            g.fillRect(10, 1, 1, 1);
            g.fillRect(1, 10, 1, 1);
            g.fillRect(10, 10, 1, 1);
        } else if (pressed || !enabled) {
            if (pressed) {
                g.setColor(MetalLookAndFeel.getPrimaryControl());
            } else {
                g.setColor(MetalLookAndFeel.getControl());
            }
            g.fillRect(2, 2, 8, 8);
            g.fillRect(4, 1, 4, 1);
            g.fillRect(4, 10, 4, 1);
            g.fillRect(1, 4, 1, 4);
            g.fillRect(10, 4, 1, 4);
        }
        if (!enabled) {
            g.setColor(MetalLookAndFeel.getInactiveControlTextColor());
        } else {
            g.setColor(MetalLookAndFeel.getControlDarkShadow());
        }
        g.drawLine(4, 0, 7, 0);
        g.drawLine(8, 1, 9, 1);
        g.drawLine(10, 2, 10, 3);
        g.drawLine(11, 4, 11, 7);
        g.drawLine(10, 8, 10, 9);
        g.drawLine(9, 10, 8, 10);
        g.drawLine(7, 11, 4, 11);
        g.drawLine(3, 10, 2, 10);
        g.drawLine(1, 9, 1, 8);
        g.drawLine(0, 7, 0, 4);
        g.drawLine(1, 3, 1, 2);
        g.drawLine(2, 1, 3, 1);
        if (pressed) {
            g.fillRect(1, 4, 1, 4);
            g.fillRect(2, 2, 1, 2);
            g.fillRect(3, 2, 1, 1);
            g.fillRect(4, 1, 4, 1);
        } else if (rollover) {
            g.setColor(MetalLookAndFeel.getPrimaryControl());
            g.fillRect(4, 1, 4, 2);
            g.fillRect(8, 2, 2, 2);
            g.fillRect(9, 4, 2, 4);
            g.fillRect(8, 8, 2, 2);
            g.fillRect(4, 9, 4, 2);
            g.fillRect(2, 8, 2, 2);
            g.fillRect(1, 4, 2, 4);
            g.fillRect(2, 2, 2, 2);
        }
        if (model.isSelected()) {
            if (enabled) {
                g.setColor(c.getForeground());
            } else {
                g.setColor(MetalLookAndFeel.getControlDarkShadow());
            }
            g.fillRect(4, 4, 4, 4);
            g.drawLine(4, 3, 7, 3);
            g.drawLine(8, 4, 8, 7);
            g.drawLine(7, 8, 4, 8);
            g.drawLine(3, 7, 3, 4);
        }
        g.translate(-x, -y);
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        if (MetalLookAndFeel.usingOcean()) {
            paintOceanIcon(c, g, x, y);
            return;
        }
        JRadioButton rb = (JRadioButton)(JRadioButton)c;
        ButtonModel model = rb.getModel();
        boolean drawDot = model.isSelected();
        Color background = c.getBackground();
        Color dotColor = c.getForeground();
        Color shadow = MetalLookAndFeel.getControlShadow();
        Color darkCircle = MetalLookAndFeel.getControlDarkShadow();
        Color whiteInnerLeftArc = MetalLookAndFeel.getControlHighlight();
        Color whiteOuterRightArc = MetalLookAndFeel.getControlHighlight();
        Color interiorColor = background;
        if (!model.isEnabled()) {
            whiteInnerLeftArc = whiteOuterRightArc = background;
            darkCircle = dotColor = shadow;
        } else if (model.isPressed() && model.isArmed()) {
            whiteInnerLeftArc = interiorColor = shadow;
        }
        g.translate(x, y);
        g.setColor(interiorColor);
        g.fillRect(2, 2, 9, 9);
        g.setColor(darkCircle);
        g.drawLine(4, 0, 7, 0);
        g.drawLine(8, 1, 9, 1);
        g.drawLine(10, 2, 10, 3);
        g.drawLine(11, 4, 11, 7);
        g.drawLine(10, 8, 10, 9);
        g.drawLine(9, 10, 8, 10);
        g.drawLine(7, 11, 4, 11);
        g.drawLine(3, 10, 2, 10);
        g.drawLine(1, 9, 1, 8);
        g.drawLine(0, 7, 0, 4);
        g.drawLine(1, 3, 1, 2);
        g.drawLine(2, 1, 3, 1);
        g.setColor(whiteInnerLeftArc);
        g.drawLine(2, 9, 2, 8);
        g.drawLine(1, 7, 1, 4);
        g.drawLine(2, 2, 2, 3);
        g.drawLine(2, 2, 3, 2);
        g.drawLine(4, 1, 7, 1);
        g.drawLine(8, 2, 9, 2);
        g.setColor(whiteOuterRightArc);
        g.drawLine(10, 1, 10, 1);
        g.drawLine(11, 2, 11, 3);
        g.drawLine(12, 4, 12, 7);
        g.drawLine(11, 8, 11, 9);
        g.drawLine(10, 10, 10, 10);
        g.drawLine(9, 11, 8, 11);
        g.drawLine(7, 12, 4, 12);
        g.drawLine(3, 11, 2, 11);
        if (drawDot) {
            g.setColor(dotColor);
            g.fillRect(4, 4, 4, 4);
            g.drawLine(4, 3, 7, 3);
            g.drawLine(8, 4, 8, 7);
            g.drawLine(7, 8, 4, 8);
            g.drawLine(3, 7, 3, 4);
        }
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return 13;
    }
    
    public int getIconHeight() {
        return 13;
    }
}
