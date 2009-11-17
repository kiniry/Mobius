package javax.swing.text.html;

import java.awt.*;
import javax.swing.SizeRequirements;
import javax.swing.text.Element;
import javax.swing.text.AttributeSet;
import javax.swing.text.StyleConstants;
import javax.swing.text.View;
import javax.swing.text.JTextComponent;

public class ParagraphView extends javax.swing.text.ParagraphView {
    
    public ParagraphView(Element elem) {
        super(elem);
    }
    
    public void setParent(View parent) {
        super.setParent(parent);
        if (parent != null) {
            setPropertiesFromAttributes();
        }
    }
    
    public AttributeSet getAttributes() {
        if (attr == null) {
            StyleSheet sheet = getStyleSheet();
            attr = sheet.getViewAttributes(this);
        }
        return attr;
    }
    
    protected void setPropertiesFromAttributes() {
        StyleSheet sheet = getStyleSheet();
        attr = sheet.getViewAttributes(this);
        painter = sheet.getBoxPainter(attr);
        if (attr != null) {
            super.setPropertiesFromAttributes();
            setInsets((short)painter.getInset(TOP, this), (short)painter.getInset(LEFT, this), (short)painter.getInset(BOTTOM, this), (short)painter.getInset(RIGHT, this));
            Object o = attr.getAttribute(CSS$Attribute.TEXT_ALIGN);
            if (o != null) {
                String ta = o.toString();
                if (ta.equals("left")) {
                    setJustification(StyleConstants.ALIGN_LEFT);
                } else if (ta.equals("center")) {
                    setJustification(StyleConstants.ALIGN_CENTER);
                } else if (ta.equals("right")) {
                    setJustification(StyleConstants.ALIGN_RIGHT);
                } else if (ta.equals("justify")) {
                    setJustification(StyleConstants.ALIGN_JUSTIFIED);
                }
            }
            cssWidth = (CSS$LengthValue)(CSS$LengthValue)attr.getAttribute(CSS$Attribute.WIDTH);
            cssHeight = (CSS$LengthValue)(CSS$LengthValue)attr.getAttribute(CSS$Attribute.HEIGHT);
        }
    }
    
    protected StyleSheet getStyleSheet() {
        HTMLDocument doc = (HTMLDocument)(HTMLDocument)getDocument();
        return doc.getStyleSheet();
    }
    
    protected SizeRequirements calculateMinorAxisRequirements(int axis, SizeRequirements r) {
        r = super.calculateMinorAxisRequirements(axis, r);
        if (!BlockView.spanSetFromAttributes(axis, r, cssWidth, cssHeight)) {
            float min = 0;
            int n = getLayoutViewCount();
            for (int i = 0; i < n; i++) {
                View v = getLayoutView(i);
                if (v instanceof InlineView) {
                    float wordSpan = ((InlineView)(InlineView)v).getLongestWordSpan();
                    min = Math.max(wordSpan, min);
                } else {
                    min = Math.max(v.getMinimumSpan(axis), min);
                }
            }
            r.minimum = Math.max(r.minimum, (int)min);
            r.preferred = Math.max(r.minimum, r.preferred);
            r.maximum = Math.max(r.preferred, r.maximum);
        } else {
            int margin = (axis == X_AXIS) ? getLeftInset() + getRightInset() : getTopInset() + getBottomInset();
            r.minimum -= margin;
            r.preferred -= margin;
            r.maximum -= margin;
        }
        return r;
    }
    
    public boolean isVisible() {
        int n = getLayoutViewCount() - 1;
        for (int i = 0; i < n; i++) {
            View v = getLayoutView(i);
            if (v.isVisible()) {
                return true;
            }
        }
        if (n > 0) {
            View v = getLayoutView(n);
            if ((v.getEndOffset() - v.getStartOffset()) == 1) {
                return false;
            }
        }
        if (getStartOffset() == getDocument().getLength()) {
            boolean editable = false;
            Component c = getContainer();
            if (c instanceof JTextComponent) {
                editable = ((JTextComponent)(JTextComponent)c).isEditable();
            }
            if (!editable) {
                return false;
            }
        }
        return true;
    }
    
    public void paint(Graphics g, Shape a) {
        if (a == null) {
            return;
        }
        Rectangle r;
        if (a instanceof Rectangle) {
            r = (Rectangle)(Rectangle)a;
        } else {
            r = a.getBounds();
        }
        painter.paint(g, r.x, r.y, r.width, r.height, this);
        super.paint(g, a);
    }
    
    public float getPreferredSpan(int axis) {
        if (!isVisible()) {
            return 0;
        }
        return super.getPreferredSpan(axis);
    }
    
    public float getMinimumSpan(int axis) {
        if (!isVisible()) {
            return 0;
        }
        return super.getMinimumSpan(axis);
    }
    
    public float getMaximumSpan(int axis) {
        if (!isVisible()) {
            return 0;
        }
        return super.getMaximumSpan(axis);
    }
    private AttributeSet attr;
    private StyleSheet$BoxPainter painter;
    private CSS$LengthValue cssWidth;
    private CSS$LengthValue cssHeight;
}
