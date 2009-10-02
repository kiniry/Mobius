package javax.swing.text;

import java.awt.*;
import javax.swing.SwingUtilities;
import javax.swing.event.*;

public class ComponentView extends View {
    
    public ComponentView(Element elem) {
        super(elem);
    }
    
    protected Component createComponent() {
        AttributeSet attr = getElement().getAttributes();
        Component comp = StyleConstants.getComponent(attr);
        return comp;
    }
    
    public final Component getComponent() {
        return createdC;
    }
    
    public void paint(Graphics g, Shape a) {
        if (c != null) {
            Rectangle alloc = (a instanceof Rectangle) ? (Rectangle)(Rectangle)a : a.getBounds();
            c.setBounds(alloc.x, alloc.y, alloc.width, alloc.height);
        }
    }
    
    public float getPreferredSpan(int axis) {
        if ((axis != X_AXIS) && (axis != Y_AXIS)) {
            throw new IllegalArgumentException("Invalid axis: " + axis);
        }
        if (c != null) {
            Dimension size = c.getPreferredSize();
            if (axis == View.X_AXIS) {
                return size.width;
            } else {
                return size.height;
            }
        }
        return 0;
    }
    
    public float getMinimumSpan(int axis) {
        if ((axis != X_AXIS) && (axis != Y_AXIS)) {
            throw new IllegalArgumentException("Invalid axis: " + axis);
        }
        if (c != null) {
            Dimension size = c.getMinimumSize();
            if (axis == View.X_AXIS) {
                return size.width;
            } else {
                return size.height;
            }
        }
        return 0;
    }
    
    public float getMaximumSpan(int axis) {
        if ((axis != X_AXIS) && (axis != Y_AXIS)) {
            throw new IllegalArgumentException("Invalid axis: " + axis);
        }
        if (c != null) {
            Dimension size = c.getMaximumSize();
            if (axis == View.X_AXIS) {
                return size.width;
            } else {
                return size.height;
            }
        }
        return 0;
    }
    
    public float getAlignment(int axis) {
        if (c != null) {
            switch (axis) {
            case View.X_AXIS: 
                return c.getAlignmentX();
            
            case View.Y_AXIS: 
                return c.getAlignmentY();
            
            }
        }
        return super.getAlignment(axis);
    }
    
    public void setParent(View p) {
        super.setParent(p);
        if (SwingUtilities.isEventDispatchThread()) {
            setComponentParent();
        } else {
            Runnable callSetComponentParent = new ComponentView$1(this);
            SwingUtilities.invokeLater(callSetComponentParent);
        }
    }
    
    void setComponentParent() {
        View p = getParent();
        if (p != null) {
            Container parent = getContainer();
            if (parent != null) {
                if (c == null) {
                    Component comp = createComponent();
                    if (comp != null) {
                        createdC = comp;
                        c = new ComponentView$Invalidator(this, comp);
                    }
                }
                if (c != null) {
                    if (c.getParent() == null) {
                        parent.add(c, this);
                    }
                }
            }
        } else {
            if (c != null) {
                Container parent = c.getParent();
                if (parent != null) {
                    parent.remove(c);
                }
            }
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
    private Component createdC;
    private Component c;
    {
    }
}
