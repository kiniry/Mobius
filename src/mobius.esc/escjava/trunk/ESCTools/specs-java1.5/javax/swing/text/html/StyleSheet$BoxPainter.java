package javax.swing.text.html;

import java.util.*;
import java.awt.*;
import java.io.*;
import java.net.*;
import javax.swing.border.*;
import javax.swing.text.*;

public class StyleSheet$BoxPainter implements Serializable {
    
    StyleSheet$BoxPainter(AttributeSet a, CSS css, StyleSheet ss) {
        
        this.ss = ss;
        this.css = css;
        border = getBorder(a);
        binsets = border.getBorderInsets(null);
        topMargin = getLength(CSS$Attribute.MARGIN_TOP, a);
        bottomMargin = getLength(CSS$Attribute.MARGIN_BOTTOM, a);
        leftMargin = getLength(CSS$Attribute.MARGIN_LEFT, a);
        rightMargin = getLength(CSS$Attribute.MARGIN_RIGHT, a);
        bg = ss.getBackground(a);
        if (ss.getBackgroundImage(a) != null) {
            bgPainter = new StyleSheet$BackgroundImagePainter(a, css, ss);
        }
    }
    
    Border getBorder(AttributeSet a) {
        Border b = StyleSheet.noBorder;
        Object o = a.getAttribute(CSS$Attribute.BORDER_STYLE);
        if (o != null) {
            String bstyle = o.toString();
            int bw = (int)getLength(CSS$Attribute.BORDER_TOP_WIDTH, a);
            if (bw > 0) {
                if (bstyle.equals("inset")) {
                    Color c = getBorderColor(a);
                    b = new BevelBorder(BevelBorder.LOWERED, c.brighter(), c.darker());
                } else if (bstyle.equals("outset")) {
                    Color c = getBorderColor(a);
                    b = new BevelBorder(BevelBorder.RAISED, c.brighter(), c.darker());
                } else if (bstyle.equals("solid")) {
                    Color c = getBorderColor(a);
                    b = new LineBorder(c);
                }
            }
        }
        return b;
    }
    
    Color getBorderColor(AttributeSet a) {
        Color color = css.getColor(a, CSS$Attribute.BORDER_COLOR);
        if (color == null) {
            color = css.getColor(a, CSS$Attribute.COLOR);
            if (color == null) {
                return Color.black;
            }
        }
        return color;
    }
    
    public float getInset(int side, View v) {
        AttributeSet a = v.getAttributes();
        float inset = 0;
        switch (side) {
        case View.LEFT: 
            inset += getOrientationMargin(StyleSheet$BoxPainter$HorizontalMargin.LEFT, leftMargin, a, isLeftToRight(v));
            inset += binsets.left;
            inset += getLength(CSS$Attribute.PADDING_LEFT, a);
            break;
        
        case View.RIGHT: 
            inset += getOrientationMargin(StyleSheet$BoxPainter$HorizontalMargin.RIGHT, rightMargin, a, isLeftToRight(v));
            inset += binsets.right;
            inset += getLength(CSS$Attribute.PADDING_RIGHT, a);
            break;
        
        case View.TOP: 
            inset += topMargin;
            inset += binsets.top;
            inset += getLength(CSS$Attribute.PADDING_TOP, a);
            break;
        
        case View.BOTTOM: 
            inset += bottomMargin;
            inset += binsets.bottom;
            inset += getLength(CSS$Attribute.PADDING_BOTTOM, a);
            break;
        
        default: 
            throw new IllegalArgumentException("Invalid side: " + side);
        
        }
        return inset;
    }
    
    public void paint(Graphics g, float x, float y, float w, float h, View v) {
        float dx = 0;
        float dy = 0;
        float dw = 0;
        float dh = 0;
        AttributeSet a = v.getAttributes();
        boolean isLeftToRight = isLeftToRight(v);
        float localLeftMargin = getOrientationMargin(StyleSheet$BoxPainter$HorizontalMargin.LEFT, leftMargin, a, isLeftToRight);
        float localRightMargin = getOrientationMargin(StyleSheet$BoxPainter$HorizontalMargin.RIGHT, rightMargin, a, isLeftToRight);
        if (!(v instanceof HTMLEditorKit$HTMLFactory$BodyBlockView)) {
            dx = localLeftMargin;
            dy = topMargin;
            dw = -(localLeftMargin + localRightMargin);
            dh = -(topMargin + bottomMargin);
        }
        if (bg != null) {
            g.setColor(bg);
            g.fillRect((int)(x + dx), (int)(y + dy), (int)(w + dw), (int)(h + dh));
        }
        if (bgPainter != null) {
            bgPainter.paint(g, x + dx, y + dy, w + dw, h + dh, v);
        }
        x += localLeftMargin;
        y += topMargin;
        w -= localLeftMargin + localRightMargin;
        h -= topMargin + bottomMargin;
        border.paintBorder(null, g, (int)x, (int)y, (int)w, (int)h);
    }
    
    float getLength(CSS$Attribute key, AttributeSet a) {
        return css.getLength(a, key, ss);
    }
    
    static boolean isLeftToRight(View v) {
        boolean ret = true;
        if (isOrientationAware(v)) {
            Container container = null;
            if (v != null && (container = v.getContainer()) != null) {
                ret = container.getComponentOrientation().isLeftToRight();
            }
        }
        return ret;
    }
    
    static boolean isOrientationAware(View v) {
        boolean ret = false;
        AttributeSet attr = null;
        Object obj = null;
        if (v != null && (attr = v.getElement().getAttributes()) != null && (obj = attr.getAttribute(StyleConstants.NameAttribute)) instanceof HTML$Tag && (obj == HTML$Tag.DIR || obj == HTML$Tag.MENU || obj == HTML$Tag.UL || obj == HTML$Tag.OL)) {
            ret = true;
        }
        return ret;
    }
    {
    }
    {
    }
    
    float getOrientationMargin(StyleSheet$BoxPainter$HorizontalMargin side, float cssMargin, AttributeSet a, boolean isLeftToRight) {
        float margin = cssMargin;
        float orientationMargin = cssMargin;
        Object cssMarginValue = null;
        switch (javax.swing.text.html.StyleSheet$1.$SwitchMap$javax$swing$text$html$StyleSheet$BoxPainter$HorizontalMargin[side.ordinal()]) {
        case 1: 
            {
                orientationMargin = (isLeftToRight) ? getLength(CSS$Attribute.MARGIN_RIGHT_LTR, a) : getLength(CSS$Attribute.MARGIN_RIGHT_RTL, a);
                cssMarginValue = a.getAttribute(CSS$Attribute.MARGIN_RIGHT);
            }
            break;
        
        case 2: 
            {
                orientationMargin = (isLeftToRight) ? getLength(CSS$Attribute.MARGIN_LEFT_LTR, a) : getLength(CSS$Attribute.MARGIN_LEFT_RTL, a);
                cssMarginValue = a.getAttribute(CSS$Attribute.MARGIN_LEFT);
            }
            break;
        
        }
        if (cssMarginValue == null && orientationMargin != Integer.MIN_VALUE) {
            margin = orientationMargin;
        }
        return margin;
    }
    float topMargin;
    float bottomMargin;
    float leftMargin;
    float rightMargin;
    short marginFlags;
    Border border;
    Insets binsets;
    CSS css;
    StyleSheet ss;
    Color bg;
    StyleSheet$BackgroundImagePainter bgPainter;
}
