package javax.swing.text.html;

import javax.swing.text.*;
import java.awt.*;

class NoFramesView extends BlockView {
    
    public NoFramesView(Element elem, int axis) {
        super(elem, axis);
        visible = false;
    }
    
    public void paint(Graphics g, Shape allocation) {
        Container host = getContainer();
        if (host != null && visible != ((JTextComponent)(JTextComponent)host).isEditable()) {
            visible = ((JTextComponent)(JTextComponent)host).isEditable();
        }
        if (!isVisible()) {
            return;
        }
        super.paint(g, allocation);
    }
    
    public void setParent(View p) {
        if (p != null) {
            Container host = p.getContainer();
            if (host != null) {
                visible = ((JTextComponent)(JTextComponent)host).isEditable();
            }
        }
        super.setParent(p);
    }
    
    public boolean isVisible() {
        return visible;
    }
    
    protected void layout(int width, int height) {
        if (!isVisible()) {
            return;
        }
        super.layout(width, height);
    }
    
    public float getPreferredSpan(int axis) {
        if (!visible) {
            return 0;
        }
        return super.getPreferredSpan(axis);
    }
    
    public float getMinimumSpan(int axis) {
        if (!visible) {
            return 0;
        }
        return super.getMinimumSpan(axis);
    }
    
    public float getMaximumSpan(int axis) {
        if (!visible) {
            return 0;
        }
        return super.getMaximumSpan(axis);
    }
    boolean visible;
}
