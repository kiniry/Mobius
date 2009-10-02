package javax.swing.plaf;

import java.awt.Color;
import javax.swing.border.*;
import javax.swing.plaf.UIResource;

public class BorderUIResource$BevelBorderUIResource extends BevelBorder implements UIResource {
    
    public BorderUIResource$BevelBorderUIResource(int bevelType) {
        super(bevelType);
    }
    
    public BorderUIResource$BevelBorderUIResource(int bevelType, Color highlight, Color shadow) {
        super(bevelType, highlight, shadow);
    }
    
    public BorderUIResource$BevelBorderUIResource(int bevelType, Color highlightOuter, Color highlightInner, Color shadowOuter, Color shadowInner) {
        super(bevelType, highlightOuter, highlightInner, shadowOuter, shadowInner);
    }
}
