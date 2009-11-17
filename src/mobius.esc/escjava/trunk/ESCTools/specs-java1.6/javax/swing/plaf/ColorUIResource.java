package javax.swing.plaf;

import java.awt.Color;
import javax.swing.plaf.UIResource;

public class ColorUIResource extends Color implements UIResource {
    
    public ColorUIResource(int r, int g, int b) {
        super(r, g, b);
    }
    
    public ColorUIResource(int rgb) {
        super(rgb);
    }
    
    public ColorUIResource(float r, float g, float b) {
        super(r, g, b);
    }
    
    public ColorUIResource(Color c) {
        super(c.getRGB(), (c.getRGB() & -16777216) != -16777216);
    }
}
