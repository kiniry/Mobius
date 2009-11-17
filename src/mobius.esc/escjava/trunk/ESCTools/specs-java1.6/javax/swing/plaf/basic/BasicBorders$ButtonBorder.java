package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import java.awt.Component;
import java.awt.Insets;
import java.awt.Color;
import java.awt.Graphics;

public class BasicBorders$ButtonBorder extends AbstractBorder implements UIResource {
    protected Color shadow;
    protected Color darkShadow;
    protected Color highlight;
    protected Color lightHighlight;
    
    public BasicBorders$ButtonBorder(Color shadow, Color darkShadow, Color highlight, Color lightHighlight) {
        
        this.shadow = shadow;
        this.darkShadow = darkShadow;
        this.highlight = highlight;
        this.lightHighlight = lightHighlight;
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        boolean isPressed = false;
        boolean isDefault = false;
        if (c instanceof AbstractButton) {
            AbstractButton b = (AbstractButton)(AbstractButton)c;
            ButtonModel model = b.getModel();
            isPressed = model.isPressed() && model.isArmed();
            if (c instanceof JButton) {
                isDefault = ((JButton)(JButton)c).isDefaultButton();
            }
        }
        BasicGraphicsUtils.drawBezel(g, x, y, width, height, isPressed, isDefault, shadow, darkShadow, highlight, lightHighlight);
    }
    
    public Insets getBorderInsets(Component c) {
        return getBorderInsets(c, new Insets(0, 0, 0, 0));
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        insets.top = 2;
        insets.left = insets.bottom = insets.right = 3;
        return insets;
    }
}
