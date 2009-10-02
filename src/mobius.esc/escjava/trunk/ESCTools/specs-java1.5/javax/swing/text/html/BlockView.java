package javax.swing.text.html;

import java.awt.*;
import javax.swing.SizeRequirements;
import javax.swing.border.*;
import javax.swing.event.DocumentEvent;
import javax.swing.text.*;

public class BlockView extends BoxView {
    
    public BlockView(Element elem, int axis) {
        super(elem, axis);
    }
    
    public void setParent(View parent) {
        super.setParent(parent);
        if (parent != null) {
            setPropertiesFromAttributes();
        }
    }
    
    protected SizeRequirements calculateMajorAxisRequirements(int axis, SizeRequirements r) {
        if (r == null) {
            r = new SizeRequirements();
        }
        if (!spanSetFromAttributes(axis, r, cssWidth, cssHeight)) {
            r = super.calculateMajorAxisRequirements(axis, r);
        } else {
            SizeRequirements parentR = super.calculateMajorAxisRequirements(axis, null);
            int margin = (axis == X_AXIS) ? getLeftInset() + getRightInset() : getTopInset() + getBottomInset();
            r.minimum -= margin;
            r.preferred -= margin;
            r.maximum -= margin;
            constrainSize(axis, r, parentR);
        }
        return r;
    }
    
    protected SizeRequirements calculateMinorAxisRequirements(int axis, SizeRequirements r) {
        if (r == null) {
            r = new SizeRequirements();
        }
        if (!spanSetFromAttributes(axis, r, cssWidth, cssHeight)) {
            r = super.calculateMinorAxisRequirements(axis, r);
        } else {
            SizeRequirements parentR = super.calculateMinorAxisRequirements(axis, null);
            int margin = (axis == X_AXIS) ? getLeftInset() + getRightInset() : getTopInset() + getBottomInset();
            r.minimum -= margin;
            r.preferred -= margin;
            r.maximum -= margin;
            constrainSize(axis, r, parentR);
        }
        if (axis == X_AXIS) {
            Object o = getAttributes().getAttribute(CSS$Attribute.TEXT_ALIGN);
            if (o != null) {
                String align = o.toString();
                if (align.equals("center")) {
                    r.alignment = 0.5F;
                } else if (align.equals("right")) {
                    r.alignment = 1.0F;
                } else {
                    r.alignment = 0.0F;
                }
            }
        }
        return r;
    }
    
    boolean isPercentage(int axis, AttributeSet a) {
        if (axis == X_AXIS) {
            if (cssWidth != null) {
                return cssWidth.isPercentage();
            }
        } else {
            if (cssHeight != null) {
                return cssHeight.isPercentage();
            }
        }
        return false;
    }
    
    static boolean spanSetFromAttributes(int axis, SizeRequirements r, CSS$LengthValue cssWidth, CSS$LengthValue cssHeight) {
        if (axis == X_AXIS) {
            if ((cssWidth != null) && (!cssWidth.isPercentage())) {
                r.minimum = r.preferred = r.maximum = (int)cssWidth.getValue();
                return true;
            }
        } else {
            if ((cssHeight != null) && (!cssHeight.isPercentage())) {
                r.minimum = r.preferred = r.maximum = (int)cssHeight.getValue();
                return true;
            }
        }
        return false;
    }
    
    protected void layoutMinorAxis(int targetSpan, int axis, int[] offsets, int[] spans) {
        int n = getViewCount();
        Object key = (axis == X_AXIS) ? CSS$Attribute.WIDTH : CSS$Attribute.HEIGHT;
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            int min = (int)v.getMinimumSpan(axis);
            int max;
            AttributeSet a = v.getAttributes();
            CSS$LengthValue lv = (CSS$LengthValue)(CSS$LengthValue)a.getAttribute(key);
            if ((lv != null) && lv.isPercentage()) {
                min = Math.max((int)lv.getValue(targetSpan), min);
                max = min;
            } else {
                max = (int)v.getMaximumSpan(axis);
            }
            if (max < targetSpan) {
                float align = v.getAlignment(axis);
                offsets[i] = (int)((targetSpan - max) * align);
                spans[i] = max;
            } else {
                offsets[i] = 0;
                spans[i] = Math.max(min, targetSpan);
            }
        }
    }
    
    public void paint(Graphics g, Shape allocation) {
        Rectangle a = (Rectangle)(Rectangle)allocation;
        painter.paint(g, a.x, a.y, a.width, a.height, this);
        super.paint(g, a);
    }
    
    public AttributeSet getAttributes() {
        if (attr == null) {
            StyleSheet sheet = getStyleSheet();
            attr = sheet.getViewAttributes(this);
        }
        return attr;
    }
    
    public int getResizeWeight(int axis) {
        switch (axis) {
        case View.X_AXIS: 
            return 1;
        
        case View.Y_AXIS: 
            return 0;
        
        default: 
            throw new IllegalArgumentException("Invalid axis: " + axis);
        
        }
    }
    
    public float getAlignment(int axis) {
        switch (axis) {
        case View.X_AXIS: 
            return 0;
        
        case View.Y_AXIS: 
            if (getViewCount() == 0) {
                return 0;
            }
            float span = getPreferredSpan(View.Y_AXIS);
            View v = getView(0);
            float above = v.getPreferredSpan(View.Y_AXIS);
            float a = (((int)span) != 0) ? (above * v.getAlignment(View.Y_AXIS)) / span : 0;
            return a;
        
        default: 
            throw new IllegalArgumentException("Invalid axis: " + axis);
        
        }
    }
    
    public void changedUpdate(DocumentEvent changes, Shape a, ViewFactory f) {
        super.changedUpdate(changes, a, f);
        int pos = changes.getOffset();
        if (pos <= getStartOffset() && (pos + changes.getLength()) >= getEndOffset()) {
            setPropertiesFromAttributes();
        }
    }
    
    public float getPreferredSpan(int axis) {
        return super.getPreferredSpan(axis);
    }
    
    public float getMinimumSpan(int axis) {
        return super.getMinimumSpan(axis);
    }
    
    public float getMaximumSpan(int axis) {
        return super.getMaximumSpan(axis);
    }
    
    protected void setPropertiesFromAttributes() {
        StyleSheet sheet = getStyleSheet();
        attr = sheet.getViewAttributes(this);
        painter = sheet.getBoxPainter(attr);
        if (attr != null) {
            setInsets((short)painter.getInset(TOP, this), (short)painter.getInset(LEFT, this), (short)painter.getInset(BOTTOM, this), (short)painter.getInset(RIGHT, this));
        }
        cssWidth = (CSS$LengthValue)(CSS$LengthValue)attr.getAttribute(CSS$Attribute.WIDTH);
        cssHeight = (CSS$LengthValue)(CSS$LengthValue)attr.getAttribute(CSS$Attribute.HEIGHT);
    }
    
    protected StyleSheet getStyleSheet() {
        HTMLDocument doc = (HTMLDocument)(HTMLDocument)getDocument();
        return doc.getStyleSheet();
    }
    
    private void constrainSize(int axis, SizeRequirements want, SizeRequirements min) {
        if (min.minimum > want.minimum) {
            want.minimum = want.preferred = min.minimum;
            want.maximum = Math.max(want.maximum, min.maximum);
        }
    }
    private AttributeSet attr;
    private StyleSheet$BoxPainter painter;
    private CSS$LengthValue cssWidth;
    private CSS$LengthValue cssHeight;
}
