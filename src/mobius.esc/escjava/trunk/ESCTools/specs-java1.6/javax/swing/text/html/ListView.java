package javax.swing.text.html;

import java.awt.*;
import javax.swing.text.*;

public class ListView extends BlockView {
    
    public ListView(Element elem) {
        super(elem, View.Y_AXIS);
    }
    
    public float getAlignment(int axis) {
        switch (axis) {
        case View.X_AXIS: 
            return 0.5F;
        
        case View.Y_AXIS: 
            return 0.5F;
        
        default: 
            throw new IllegalArgumentException("Invalid axis: " + axis);
        
        }
    }
    
    public void paint(Graphics g, Shape allocation) {
        super.paint(g, allocation);
        Rectangle alloc = allocation.getBounds();
        Rectangle clip = g.getClipBounds();
        if ((clip.x + clip.width) < (alloc.x + getLeftInset())) {
            Rectangle childRect = alloc;
            alloc = getInsideAllocation(allocation);
            int n = getViewCount();
            int endY = clip.y + clip.height;
            for (int i = 0; i < n; i++) {
                childRect.setBounds(alloc);
                childAllocation(i, childRect);
                if (childRect.y < endY) {
                    if ((childRect.y + childRect.height) >= clip.y) {
                        listPainter.paint(g, childRect.x, childRect.y, childRect.width, childRect.height, this, i);
                    }
                } else {
                    break;
                }
            }
        }
    }
    
    protected void paintChild(Graphics g, Rectangle alloc, int index) {
        listPainter.paint(g, alloc.x, alloc.y, alloc.width, alloc.height, this, index);
        super.paintChild(g, alloc, index);
    }
    
    protected void setPropertiesFromAttributes() {
        super.setPropertiesFromAttributes();
        listPainter = getStyleSheet().getListPainter(getAttributes());
    }
    private StyleSheet$ListPainter listPainter;
}
