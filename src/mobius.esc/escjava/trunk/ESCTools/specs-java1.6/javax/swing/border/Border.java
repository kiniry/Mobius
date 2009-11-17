package javax.swing.border;

import java.awt.Graphics;
import java.awt.Insets;
import java.awt.Component;

public interface Border {
    
    void paintBorder(Component c, Graphics g, int x, int y, int width, int height);
    
    Insets getBorderInsets(Component c);
    
    boolean isBorderOpaque();
}
