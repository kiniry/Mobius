package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import java.awt.Component;
import java.awt.Insets;
import java.awt.Color;
import java.awt.Graphics;

public class BasicBorders$RadioButtonBorder extends BasicBorders$ButtonBorder {
    
    public BasicBorders$RadioButtonBorder(Color shadow, Color darkShadow, Color highlight, Color lightHighlight) {
        super(shadow, darkShadow, highlight, lightHighlight);
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        if (c instanceof AbstractButton) {
            AbstractButton b = (AbstractButton)(AbstractButton)c;
            ButtonModel model = b.getModel();
            if (model.isArmed() && model.isPressed() || model.isSelected()) {
                BasicGraphicsUtils.drawLoweredBezel(g, x, y, width, height, shadow, darkShadow, highlight, lightHighlight);
            } else {
                BasicGraphicsUtils.drawBezel(g, x, y, width, height, false, b.isFocusPainted() && b.hasFocus(), shadow, darkShadow, highlight, lightHighlight);
            }
        } else {
            BasicGraphicsUtils.drawBezel(g, x, y, width, height, false, false, shadow, darkShadow, highlight, lightHighlight);
        }
    }
    
    public Insets getBorderInsets(Component c) {
        return getBorderInsets(c, new Insets(0, 0, 0, 0));
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        insets.top = insets.left = insets.bottom = insets.right = 2;
        return insets;
    }
}
