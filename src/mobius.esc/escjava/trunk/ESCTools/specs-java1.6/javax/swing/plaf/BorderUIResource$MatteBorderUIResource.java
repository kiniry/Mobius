package javax.swing.plaf;

import java.awt.Color;
import javax.swing.border.*;
import javax.swing.Icon;
import javax.swing.plaf.UIResource;

public class BorderUIResource$MatteBorderUIResource extends MatteBorder implements UIResource {
    
    public BorderUIResource$MatteBorderUIResource(int top, int left, int bottom, int right, Color color) {
        super(top, left, bottom, right, color);
    }
    
    public BorderUIResource$MatteBorderUIResource(int top, int left, int bottom, int right, Icon tileIcon) {
        super(top, left, bottom, right, tileIcon);
    }
    
    public BorderUIResource$MatteBorderUIResource(Icon tileIcon) {
        super(tileIcon);
    }
}
