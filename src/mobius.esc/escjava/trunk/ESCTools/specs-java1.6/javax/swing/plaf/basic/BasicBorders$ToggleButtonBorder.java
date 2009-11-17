package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import java.awt.Component;
import java.awt.Insets;
import java.awt.Color;
import java.awt.Graphics;

public class BasicBorders$ToggleButtonBorder extends BasicBorders$ButtonBorder {
    
    public BasicBorders$ToggleButtonBorder(Color shadow, Color darkShadow, Color highlight, Color lightHighlight) {
        super(shadow, darkShadow, highlight, lightHighlight);
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        BasicGraphicsUtils.drawBezel(g, x, y, width, height, false, false, shadow, darkShadow, highlight, lightHighlight);
    }
    
    public Insets getBorderInsets(Component c) {
        return new Insets(2, 2, 2, 2);
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        insets.top = insets.left = insets.bottom = insets.right = 2;
        return insets;
    }
}
