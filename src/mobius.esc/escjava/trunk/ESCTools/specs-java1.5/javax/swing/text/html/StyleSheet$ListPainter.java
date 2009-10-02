package javax.swing.text.html;

import com.sun.java.swing.SwingUtilities2;
import java.util.*;
import java.awt.*;
import java.io.*;
import java.net.*;
import javax.swing.Icon;
import javax.swing.ImageIcon;
import javax.swing.border.*;
import javax.swing.text.*;

public class StyleSheet$ListPainter implements Serializable {
    
    StyleSheet$ListPainter(AttributeSet attr, StyleSheet ss) {
        
        this.ss = ss;
        String imgstr = (String)(String)attr.getAttribute(CSS$Attribute.LIST_STYLE_IMAGE);
        type = null;
        if (imgstr != null && !imgstr.equals("none")) {
            String tmpstr = null;
            try {
                StringTokenizer st = new StringTokenizer(imgstr, "()");
                if (st.hasMoreTokens()) tmpstr = st.nextToken();
                if (st.hasMoreTokens()) tmpstr = st.nextToken();
                URL u = new URL(tmpstr);
                img = new ImageIcon(u);
            } catch (MalformedURLException e) {
                if (tmpstr != null && ss != null && ss.getBase() != null) {
                    try {
                        URL u = new URL(ss.getBase(), tmpstr);
                        img = new ImageIcon(u);
                    } catch (MalformedURLException murle) {
                        img = null;
                    }
                } else {
                    img = null;
                }
            }
        }
        if (img == null) {
            type = (CSS$Value)(CSS$Value)attr.getAttribute(CSS$Attribute.LIST_STYLE_TYPE);
        }
        start = 1;
        paintRect = new Rectangle();
    }
    
    private CSS$Value getChildType(View childView) {
        CSS$Value childtype = (CSS$Value)(CSS$Value)childView.getAttributes().getAttribute(CSS$Attribute.LIST_STYLE_TYPE);
        if (childtype == null) {
            if (type == null) {
                View v = childView.getParent();
                HTMLDocument doc = (HTMLDocument)(HTMLDocument)v.getDocument();
                if (doc.matchNameAttribute(v.getElement().getAttributes(), HTML$Tag.OL)) {
                    childtype = CSS$Value.DECIMAL;
                } else {
                    childtype = CSS$Value.DISC;
                }
            } else {
                childtype = type;
            }
        }
        return childtype;
    }
    
    private void getStart(View parent) {
        checkedForStart = true;
        Element element = parent.getElement();
        if (element != null) {
            AttributeSet attr = element.getAttributes();
            Object startValue;
            if (attr != null && attr.isDefined(HTML$Attribute.START) && (startValue = attr.getAttribute(HTML$Attribute.START)) != null && (startValue instanceof String)) {
                try {
                    start = Integer.parseInt((String)(String)startValue);
                } catch (NumberFormatException nfe) {
                }
            }
        }
    }
    
    private int getRenderIndex(View parentView, int childIndex) {
        if (!checkedForStart) {
            getStart(parentView);
        }
        int retIndex = childIndex;
        for (int counter = childIndex; counter >= 0; counter--) {
            AttributeSet as = parentView.getElement().getElement(counter).getAttributes();
            if (as.getAttribute(StyleConstants.NameAttribute) != HTML$Tag.LI) {
                retIndex--;
            } else if (as.isDefined(HTML$Attribute.VALUE)) {
                Object value = as.getAttribute(HTML$Attribute.VALUE);
                if (value != null && (value instanceof String)) {
                    try {
                        int iValue = Integer.parseInt((String)(String)value);
                        return retIndex - counter + iValue;
                    } catch (NumberFormatException nfe) {
                    }
                }
            }
        }
        return retIndex + start;
    }
    
    public void paint(Graphics g, float x, float y, float w, float h, View v, int item) {
        View cv = v.getView(item);
        Object name = cv.getElement().getAttributes().getAttribute(StyleConstants.NameAttribute);
        if (!(name instanceof HTML$Tag) || name != HTML$Tag.LI) {
            return;
        }
        isLeftToRight = cv.getContainer().getComponentOrientation().isLeftToRight();
        float align = 0;
        if (cv.getViewCount() > 0) {
            View pView = cv.getView(0);
            Object cName = pView.getElement().getAttributes().getAttribute(StyleConstants.NameAttribute);
            if ((cName == HTML$Tag.P || cName == HTML$Tag.IMPLIED) && pView.getViewCount() > 0) {
                paintRect.setBounds((int)x, (int)y, (int)w, (int)h);
                Shape shape = cv.getChildAllocation(0, paintRect);
                if (shape != null && (shape = pView.getView(0).getChildAllocation(0, shape)) != null) {
                    Rectangle rect = (shape instanceof Rectangle) ? (Rectangle)(Rectangle)shape : shape.getBounds();
                    align = pView.getView(0).getAlignment(View.Y_AXIS);
                    y = rect.y;
                    h = rect.height;
                }
            }
        }
        if (ss != null) {
            g.setColor(ss.getForeground(cv.getAttributes()));
        } else {
            g.setColor(Color.black);
        }
        if (img != null) {
            drawIcon(g, (int)x, (int)y, (int)w, (int)h, align, v.getContainer());
            return;
        }
        CSS$Value childtype = getChildType(cv);
        Font font = ((StyledDocument)(StyledDocument)cv.getDocument()).getFont(cv.getAttributes());
        if (font != null) {
            g.setFont(font);
        }
        if (childtype == CSS$Value.SQUARE || childtype == CSS$Value.CIRCLE || childtype == CSS$Value.DISC) {
            drawShape(g, childtype, (int)x, (int)y, (int)w, (int)h, align);
        } else if (childtype == CSS$Value.DECIMAL) {
            drawLetter(g, '1', (int)x, (int)y, (int)w, (int)h, align, getRenderIndex(v, item));
        } else if (childtype == CSS$Value.LOWER_ALPHA) {
            drawLetter(g, 'a', (int)x, (int)y, (int)w, (int)h, align, getRenderIndex(v, item));
        } else if (childtype == CSS$Value.UPPER_ALPHA) {
            drawLetter(g, 'A', (int)x, (int)y, (int)w, (int)h, align, getRenderIndex(v, item));
        } else if (childtype == CSS$Value.LOWER_ROMAN) {
            drawLetter(g, 'i', (int)x, (int)y, (int)w, (int)h, align, getRenderIndex(v, item));
        } else if (childtype == CSS$Value.UPPER_ROMAN) {
            drawLetter(g, 'I', (int)x, (int)y, (int)w, (int)h, align, getRenderIndex(v, item));
        }
    }
    
    void drawIcon(Graphics g, int ax, int ay, int aw, int ah, float align, Component c) {
        int gap = isLeftToRight ? -(img.getIconWidth() + bulletgap) : (aw + bulletgap);
        int x = ax + gap;
        int y = Math.max(ay, ay + (int)(align * ah) - img.getIconHeight());
        img.paintIcon(c, g, x, y);
    }
    
    void drawShape(Graphics g, CSS$Value type, int ax, int ay, int aw, int ah, float align) {
        int gap = isLeftToRight ? -(bulletgap + 8) : (aw + bulletgap);
        int x = ax + gap;
        int y = Math.max(ay, ay + (int)(align * ah) - 8);
        if (type == CSS$Value.SQUARE) {
            g.drawRect(x, y, 8, 8);
        } else if (type == CSS$Value.CIRCLE) {
            g.drawOval(x, y, 8, 8);
        } else {
            g.fillOval(x, y, 8, 8);
        }
    }
    
    void drawLetter(Graphics g, char letter, int ax, int ay, int aw, int ah, float align, int index) {
        String str = formatItemNum(index, letter);
        str = isLeftToRight ? str + "." : "." + str;
        FontMetrics fm = SwingUtilities2.getFontMetrics(null, g);
        int stringwidth = SwingUtilities2.stringWidth(null, fm, str);
        int gap = isLeftToRight ? -(stringwidth + bulletgap) : (aw + bulletgap);
        int x = ax + gap;
        int y = Math.max(ay + fm.getAscent(), ay + (int)(ah * align));
        SwingUtilities2.drawString(null, g, str, x, y);
    }
    
    String formatItemNum(int itemNum, char type) {
        String numStyle = "1";
        boolean uppercase = false;
        String formattedNum;
        switch (type) {
        case '1': 
        
        default: 
            formattedNum = String.valueOf(itemNum);
            break;
        
        case 'A': 
            uppercase = true;
        
        case 'a': 
            formattedNum = formatAlphaNumerals(itemNum);
            break;
        
        case 'I': 
            uppercase = true;
        
        case 'i': 
            formattedNum = formatRomanNumerals(itemNum);
        
        }
        if (uppercase) {
            formattedNum = formattedNum.toUpperCase();
        }
        return formattedNum;
    }
    
    String formatAlphaNumerals(int itemNum) {
        String result = "";
        if (itemNum > 26) {
            result = formatAlphaNumerals(itemNum / 26) + formatAlphaNumerals(itemNum % 26);
        } else {
            result = String.valueOf((char)('a' + itemNum - 1));
        }
        return result;
    }
    static final char[][] romanChars = {{'i', 'v'}, {'x', 'l'}, {'c', 'd'}, {'m', '?'}};
    
    String formatRomanNumerals(int num) {
        return formatRomanNumerals(0, num);
    }
    
    String formatRomanNumerals(int level, int num) {
        if (num < 10) {
            return formatRomanDigit(level, num);
        } else {
            return formatRomanNumerals(level + 1, num / 10) + formatRomanDigit(level, num % 10);
        }
    }
    
    String formatRomanDigit(int level, int digit) {
        String result = "";
        if (digit == 9) {
            result = result + romanChars[level][0];
            result = result + romanChars[level + 1][0];
            return result;
        } else if (digit == 4) {
            result = result + romanChars[level][0];
            result = result + romanChars[level][1];
            return result;
        } else if (digit >= 5) {
            result = result + romanChars[level][1];
            digit -= 5;
        }
        for (int i = 0; i < digit; i++) {
            result = result + romanChars[level][0];
        }
        return result;
    }
    private Rectangle paintRect;
    private boolean checkedForStart;
    private int start;
    private CSS$Value type;
    URL imageurl;
    private StyleSheet ss = null;
    Icon img = null;
    private int bulletgap = 5;
    private boolean isLeftToRight;
}
