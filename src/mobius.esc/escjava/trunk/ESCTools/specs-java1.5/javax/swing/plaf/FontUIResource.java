package javax.swing.plaf;

import java.awt.Font;
import javax.swing.plaf.UIResource;
import sun.font.FontManager;

public class FontUIResource extends Font implements UIResource {
    
    public FontUIResource(String name, int style, int size) {
        super(name, style, size);
    }
    
    public FontUIResource(Font font) {
        super(font.getName(), font.getStyle(), font.getSize());
        FontManager.setSameHandle(font, this);
    }
}
