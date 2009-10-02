package javax.swing.text;

import java.awt.*;
import javax.swing.Icon;
import javax.swing.event.*;

public class IconView extends View {
    
    public IconView(Element elem) {
        super(elem);
        AttributeSet attr = elem.getAttributes();
        c = StyleConstants.getIcon(attr);
    }
    
    public void paint(Graphics g, Shape a) {
        Rectangle alloc = a.getBounds();
        c.paintIcon(getContainer(), g, alloc.x, alloc.y);
    }
    
    public float getPreferredSpan(int axis) {
        switch (axis) {
        case View.X_AXIS: 
            return c.getIconWidth();
        
        case View.Y_AXIS: 
            return c.getIconHeight();
        
        default: 
            throw new IllegalArgumentException("Invalid axis: " + axis);
        
        }
    }
    
    public float getAlignment(int axis) {
        switch (axis) {
        case View.Y_AXIS: 
            return 1;
        
        default: 
            return super.getAlignment(axis);
        
        }
    }
    
    public Shape modelToView(int pos, Shape a, Position$Bias b) throws BadLocationException {
        int p0 = getStartOffset();
        int p1 = getEndOffset();
        if ((pos >= p0) && (pos <= p1)) {
            Rectangle r = a.getBounds();
            if (pos == p1) {
                r.x += r.width;
            }
            r.width = 0;
            return r;
        }
        throw new BadLocationException(pos + " not in range " + p0 + "," + p1, pos);
    }
    
    public int viewToModel(float x, float y, Shape a, Position$Bias[] bias) {
        Rectangle alloc = (Rectangle)(Rectangle)a;
        if (x < alloc.x + (alloc.width / 2)) {
            bias[0] = Position$Bias.Forward;
            return getStartOffset();
        }
        bias[0] = Position$Bias.Backward;
        return getEndOffset();
    }
    private Icon c;
}
