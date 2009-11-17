package javax.swing.text.html;

import java.awt.*;
import javax.swing.event.DocumentEvent;
import javax.swing.text.*;
import java.lang.Integer;

class HRuleView extends View {
    
    public HRuleView(Element elem) {
        super(elem);
        setPropertiesFromAttributes();
    }
    
    protected void setPropertiesFromAttributes() {
        StyleSheet sheet = ((HTMLDocument)(HTMLDocument)getDocument()).getStyleSheet();
        AttributeSet eAttr = getElement().getAttributes();
        attr = sheet.getViewAttributes(this);
        alignment = StyleConstants.ALIGN_CENTER;
        size = 0;
        noshade = null;
        widthValue = null;
        if (attr != null) {
            if (attr.getAttribute(StyleConstants.Alignment) != null) {
                alignment = StyleConstants.getAlignment(attr);
            }
            noshade = (String)(String)eAttr.getAttribute(HTML$Attribute.NOSHADE);
            Object value = eAttr.getAttribute(HTML$Attribute.SIZE);
            if (value != null && (value instanceof String)) size = Integer.parseInt((String)(String)value);
            value = attr.getAttribute(CSS$Attribute.WIDTH);
            if (value != null && (value instanceof CSS$LengthValue)) {
                widthValue = (CSS$LengthValue)(CSS$LengthValue)value;
            }
            topMargin = getLength(CSS$Attribute.MARGIN_TOP, attr);
            bottomMargin = getLength(CSS$Attribute.MARGIN_BOTTOM, attr);
            leftMargin = getLength(CSS$Attribute.MARGIN_LEFT, attr);
            rightMargin = getLength(CSS$Attribute.MARGIN_RIGHT, attr);
        } else {
            topMargin = bottomMargin = leftMargin = rightMargin = 0;
        }
        size = Math.max(2, size);
    }
    
    private float getLength(CSS$Attribute key, AttributeSet a) {
        CSS$LengthValue lv = (CSS$LengthValue)(CSS$LengthValue)a.getAttribute(key);
        float len = (lv != null) ? lv.getValue() : 0;
        return len;
    }
    
    public void paint(Graphics g, Shape a) {
        Rectangle alloc = (a instanceof Rectangle) ? (Rectangle)(Rectangle)a : a.getBounds();
        int x = 0;
        int y = alloc.y + SPACE_ABOVE + (int)topMargin;
        int width = alloc.width - (int)(leftMargin + rightMargin);
        if (widthValue != null) {
            width = (int)widthValue.getValue((float)width);
        }
        int height = alloc.height - (SPACE_ABOVE + SPACE_BELOW + (int)topMargin + (int)bottomMargin);
        if (size > 0) height = size;
        switch (alignment) {
        case StyleConstants.ALIGN_CENTER: 
            x = alloc.x + (alloc.width / 2) - (width / 2);
            break;
        
        case StyleConstants.ALIGN_RIGHT: 
            x = alloc.x + alloc.width - width - (int)rightMargin;
            break;
        
        case StyleConstants.ALIGN_LEFT: 
        
        default: 
            x = alloc.x + (int)leftMargin;
            break;
        
        }
        if (noshade != null) {
            g.setColor(Color.black);
            g.fillRect(x, y, width, height);
        } else {
            Color bg = getContainer().getBackground();
            Color bottom;
            Color top;
            if (bg == null || bg.equals(Color.white)) {
                top = Color.darkGray;
                bottom = Color.lightGray;
            } else {
                top = Color.darkGray;
                bottom = Color.white;
            }
            g.setColor(bottom);
            g.drawLine(x + width - 1, y, x + width - 1, y + height - 1);
            g.drawLine(x, y + height - 1, x + width - 1, y + height - 1);
            g.setColor(top);
            g.drawLine(x, y, x + width - 1, y);
            g.drawLine(x, y, x, y + height - 1);
        }
    }
    
    public float getPreferredSpan(int axis) {
        switch (axis) {
        case View.X_AXIS: 
            return 1;
        
        case View.Y_AXIS: 
            if (size > 0) {
                return size + SPACE_ABOVE + SPACE_BELOW + topMargin + bottomMargin;
            } else {
                if (noshade != null) {
                    return 2 + SPACE_ABOVE + SPACE_BELOW + topMargin + bottomMargin;
                } else {
                    return SPACE_ABOVE + SPACE_BELOW + topMargin + bottomMargin;
                }
            }
        
        default: 
            throw new IllegalArgumentException("Invalid axis: " + axis);
        
        }
    }
    
    public int getResizeWeight(int axis) {
        if (axis == View.X_AXIS) {
            return 1;
        } else if (axis == View.Y_AXIS) {
            return 0;
        } else {
            return 0;
        }
    }
    
    public int getBreakWeight(int axis, float pos, float len) {
        if (axis == X_AXIS) {
            return ForcedBreakWeight;
        }
        return BadBreakWeight;
    }
    
    public View breakView(int axis, int offset, float pos, float len) {
        return null;
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
        return null;
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
    
    public AttributeSet getAttributes() {
        return attr;
    }
    
    public void changedUpdate(DocumentEvent changes, Shape a, ViewFactory f) {
        super.changedUpdate(changes, a, f);
        int pos = changes.getOffset();
        if (pos <= getStartOffset() && (pos + changes.getLength()) >= getEndOffset()) {
            setPropertiesFromAttributes();
        }
    }
    private float topMargin;
    private float bottomMargin;
    private float leftMargin;
    private float rightMargin;
    private int alignment = StyleConstants.ALIGN_CENTER;
    private String noshade = null;
    private int size = 0;
    private CSS$LengthValue widthValue;
    private static final int SPACE_ABOVE = 3;
    private static final int SPACE_BELOW = 3;
    private AttributeSet attr;
}
