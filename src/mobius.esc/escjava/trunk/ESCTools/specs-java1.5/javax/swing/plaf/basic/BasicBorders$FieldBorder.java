package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import javax.swing.text.JTextComponent;
import java.awt.Component;
import java.awt.Insets;
import java.awt.Color;
import java.awt.Graphics;

public class BasicBorders$FieldBorder extends AbstractBorder implements UIResource {
    protected Color shadow;
    protected Color darkShadow;
    protected Color highlight;
    protected Color lightHighlight;
    
    public BasicBorders$FieldBorder(Color shadow, Color darkShadow, Color highlight, Color lightHighlight) {
        
        this.shadow = shadow;
        this.highlight = highlight;
        this.darkShadow = darkShadow;
        this.lightHighlight = lightHighlight;
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        BasicGraphicsUtils.drawEtchedRect(g, x, y, width, height, shadow, darkShadow, highlight, lightHighlight);
    }
    
    public Insets getBorderInsets(Component c) {
        return getBorderInsets(c, new Insets(0, 0, 0, 0));
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        Insets margin = null;
        if (c instanceof JTextComponent) {
            margin = ((JTextComponent)(JTextComponent)c).getMargin();
        }
        insets.top = margin != null ? 2 + margin.top : 2;
        insets.left = margin != null ? 2 + margin.left : 2;
        insets.bottom = margin != null ? 2 + margin.bottom : 2;
        insets.right = margin != null ? 2 + margin.right : 2;
        return insets;
    }
}
