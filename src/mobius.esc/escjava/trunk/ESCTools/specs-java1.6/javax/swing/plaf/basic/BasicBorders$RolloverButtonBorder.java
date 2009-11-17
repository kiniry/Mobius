package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import java.awt.Component;
import java.awt.Color;
import java.awt.Graphics;

public class BasicBorders$RolloverButtonBorder extends BasicBorders$ButtonBorder {
    
    public BasicBorders$RolloverButtonBorder(Color shadow, Color darkShadow, Color highlight, Color lightHighlight) {
        super(shadow, darkShadow, highlight, lightHighlight);
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int w, int h) {
        AbstractButton b = (AbstractButton)(AbstractButton)c;
        ButtonModel model = b.getModel();
        Color shade = shadow;
        Component p = b.getParent();
        if (p != null && p.getBackground().equals(shadow)) {
            shade = darkShadow;
        }
        if ((model.isRollover() && !(model.isPressed() && !model.isArmed())) || model.isSelected()) {
            Color oldColor = g.getColor();
            g.translate(x, y);
            if (model.isPressed() && model.isArmed() || model.isSelected()) {
                g.setColor(shade);
                g.drawRect(0, 0, w - 1, h - 1);
                g.setColor(lightHighlight);
                g.drawLine(w - 1, 0, w - 1, h - 1);
                g.drawLine(0, h - 1, w - 1, h - 1);
            } else {
                g.setColor(lightHighlight);
                g.drawRect(0, 0, w - 1, h - 1);
                g.setColor(shade);
                g.drawLine(w - 1, 0, w - 1, h - 1);
                g.drawLine(0, h - 1, w - 1, h - 1);
            }
            g.translate(-x, -y);
            g.setColor(oldColor);
        }
    }
}
