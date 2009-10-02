package javax.swing;

import com.sun.java.swing.SwingUtilities2;
import sun.swing.UIAction;
import java.applet.*;
import java.awt.*;
import java.awt.event.*;
import java.lang.reflect.*;
import javax.accessibility.*;
import javax.swing.event.MenuDragMouseEvent;
import javax.swing.plaf.UIResource;
import javax.swing.text.View;
import sun.awt.AppContext;

public class SwingUtilities implements SwingConstants {
    private static boolean canAccessEventQueue = false;
    private static boolean eventQueueTested = false;
    
    public static final boolean isRectangleContainingRectangle(Rectangle a, Rectangle b) {
        if (b.x >= a.x && (b.x + b.width) <= (a.x + a.width) && b.y >= a.y && (b.y + b.height) <= (a.y + a.height)) {
            return true;
        }
        return false;
    }
    
    public static Rectangle getLocalBounds(Component aComponent) {
        Rectangle b = new Rectangle(aComponent.getBounds());
        b.x = b.y = 0;
        return b;
    }
    
    public static Window getWindowAncestor(Component c) {
        for (Container p = c.getParent(); p != null; p = p.getParent()) {
            if (p instanceof Window) {
                return (Window)(Window)p;
            }
        }
        return null;
    }
    
    static Point convertScreenLocationToParent(Container parent, int x, int y) {
        for (Container p = parent; p != null; p = p.getParent()) {
            if (p instanceof Window) {
                Point point = new Point(x, y);
                SwingUtilities.convertPointFromScreen(point, parent);
                return point;
            }
        }
        throw new Error("convertScreenLocationToParent: no window ancestor");
    }
    
    public static Point convertPoint(Component source, Point aPoint, Component destination) {
        Point p;
        if (source == null && destination == null) return aPoint;
        if (source == null) {
            source = getWindowAncestor(destination);
            if (source == null) throw new Error("Source component not connected to component tree hierarchy");
        }
        p = new Point(aPoint);
        convertPointToScreen(p, source);
        if (destination == null) {
            destination = getWindowAncestor(source);
            if (destination == null) throw new Error("Destination component not connected to component tree hierarchy");
        }
        convertPointFromScreen(p, destination);
        return p;
    }
    
    public static Point convertPoint(Component source, int x, int y, Component destination) {
        Point point = new Point(x, y);
        return convertPoint(source, point, destination);
    }
    
    public static Rectangle convertRectangle(Component source, Rectangle aRectangle, Component destination) {
        Point point = new Point(aRectangle.x, aRectangle.y);
        point = convertPoint(source, point, destination);
        return new Rectangle(point.x, point.y, aRectangle.width, aRectangle.height);
    }
    
    public static Container getAncestorOfClass(Class c, Component comp) {
        if (comp == null || c == null) return null;
        Container parent = comp.getParent();
        while (parent != null && !(c.isInstance(parent))) parent = parent.getParent();
        return parent;
    }
    
    public static Container getAncestorNamed(String name, Component comp) {
        if (comp == null || name == null) return null;
        Container parent = comp.getParent();
        while (parent != null && !(name.equals(parent.getName()))) parent = parent.getParent();
        return parent;
    }
    
    public static Component getDeepestComponentAt(Component parent, int x, int y) {
        if (!parent.contains(x, y)) {
            return null;
        }
        if (parent instanceof Container) {
            Component[] components = ((Container)(Container)parent).getComponents();
            for (int i = 0; i < components.length; i++) {
                Component comp = components[i];
                if (comp != null && comp.isVisible()) {
                    Point loc = comp.getLocation();
                    if (comp instanceof Container) {
                        comp = getDeepestComponentAt(comp, x - loc.x, y - loc.y);
                    } else {
                        comp = comp.getComponentAt(x - loc.x, y - loc.y);
                    }
                    if (comp != null && comp.isVisible()) {
                        return comp;
                    }
                }
            }
        }
        return parent;
    }
    
    public static MouseEvent convertMouseEvent(Component source, MouseEvent sourceEvent, Component destination) {
        Point p = convertPoint(source, new Point(sourceEvent.getX(), sourceEvent.getY()), destination);
        Component newSource;
        if (destination != null) newSource = destination; else newSource = source;
        MouseEvent newEvent;
        if (sourceEvent instanceof MouseWheelEvent) {
            MouseWheelEvent sourceWheelEvent = (MouseWheelEvent)(MouseWheelEvent)sourceEvent;
            newEvent = new MouseWheelEvent(newSource, sourceWheelEvent.getID(), sourceWheelEvent.getWhen(), sourceWheelEvent.getModifiers(), p.x, p.y, sourceWheelEvent.getClickCount(), sourceWheelEvent.isPopupTrigger(), sourceWheelEvent.getScrollType(), sourceWheelEvent.getScrollAmount(), sourceWheelEvent.getWheelRotation());
        } else if (sourceEvent instanceof MenuDragMouseEvent) {
            MenuDragMouseEvent sourceMenuDragEvent = (MenuDragMouseEvent)(MenuDragMouseEvent)sourceEvent;
            newEvent = new MenuDragMouseEvent(newSource, sourceMenuDragEvent.getID(), sourceMenuDragEvent.getWhen(), sourceMenuDragEvent.getModifiers(), p.x, p.y, sourceMenuDragEvent.getClickCount(), sourceMenuDragEvent.isPopupTrigger(), sourceMenuDragEvent.getPath(), sourceMenuDragEvent.getMenuSelectionManager());
        } else {
            newEvent = new MouseEvent(newSource, sourceEvent.getID(), sourceEvent.getWhen(), sourceEvent.getModifiers(), p.x, p.y, sourceEvent.getClickCount(), sourceEvent.isPopupTrigger());
        }
        return newEvent;
    }
    
    public static void convertPointToScreen(Point p, Component c) {
        Rectangle b;
        int x;
        int y;
        do {
            if (c instanceof JComponent) {
                x = ((JComponent)(JComponent)c).getX();
                y = ((JComponent)(JComponent)c).getY();
            } else if (c instanceof java.applet.Applet || c instanceof java.awt.Window) {
                try {
                    Point pp = c.getLocationOnScreen();
                    x = pp.x;
                    y = pp.y;
                } catch (IllegalComponentStateException icse) {
                    x = c.getX();
                    y = c.getY();
                }
            } else {
                x = c.getX();
                y = c.getY();
            }
            p.x += x;
            p.y += y;
            if (c instanceof java.awt.Window || c instanceof java.applet.Applet) break;
            c = c.getParent();
        }         while (c != null);
    }
    
    public static void convertPointFromScreen(Point p, Component c) {
        Rectangle b;
        int x;
        int y;
        do {
            if (c instanceof JComponent) {
                x = ((JComponent)(JComponent)c).getX();
                y = ((JComponent)(JComponent)c).getY();
            } else if (c instanceof java.applet.Applet || c instanceof java.awt.Window) {
                try {
                    Point pp = c.getLocationOnScreen();
                    x = pp.x;
                    y = pp.y;
                } catch (IllegalComponentStateException icse) {
                    x = c.getX();
                    y = c.getY();
                }
            } else {
                x = c.getX();
                y = c.getY();
            }
            p.x -= x;
            p.y -= y;
            if (c instanceof java.awt.Window || c instanceof java.applet.Applet) break;
            c = c.getParent();
        }         while (c != null);
    }
    
    public static Window windowForComponent(Component c) {
        return getWindowAncestor(c);
    }
    
    public static boolean isDescendingFrom(Component a, Component b) {
        if (a == b) return true;
        for (Container p = a.getParent(); p != null; p = p.getParent()) if (p == b) return true;
        return false;
    }
    
    public static Rectangle computeIntersection(int x, int y, int width, int height, Rectangle dest) {
        int x1 = (x > dest.x) ? x : dest.x;
        int x2 = ((x + width) < (dest.x + dest.width)) ? (x + width) : (dest.x + dest.width);
        int y1 = (y > dest.y) ? y : dest.y;
        int y2 = ((y + height) < (dest.y + dest.height) ? (y + height) : (dest.y + dest.height));
        dest.x = x1;
        dest.y = y1;
        dest.width = x2 - x1;
        dest.height = y2 - y1;
        if (dest.width < 0 || dest.height < 0) {
            dest.x = dest.y = dest.width = dest.height = 0;
        }
        return dest;
    }
    
    public static Rectangle computeUnion(int x, int y, int width, int height, Rectangle dest) {
        int x1 = (x < dest.x) ? x : dest.x;
        int x2 = ((x + width) > (dest.x + dest.width)) ? (x + width) : (dest.x + dest.width);
        int y1 = (y < dest.y) ? y : dest.y;
        int y2 = ((y + height) > (dest.y + dest.height)) ? (y + height) : (dest.y + dest.height);
        dest.x = x1;
        dest.y = y1;
        dest.width = (x2 - x1);
        dest.height = (y2 - y1);
        return dest;
    }
    
    public static Rectangle[] computeDifference(Rectangle rectA, Rectangle rectB) {
        if (rectB == null || !rectA.intersects(rectB) || isRectangleContainingRectangle(rectB, rectA)) {
            return new Rectangle[0];
        }
        Rectangle t = new Rectangle();
        Rectangle a = null;
        Rectangle b = null;
        Rectangle c = null;
        Rectangle d = null;
        Rectangle[] result;
        int rectCount = 0;
        if (isRectangleContainingRectangle(rectA, rectB)) {
            t.x = rectA.x;
            t.y = rectA.y;
            t.width = rectB.x - rectA.x;
            t.height = rectA.height;
            if (t.width > 0 && t.height > 0) {
                a = new Rectangle(t);
                rectCount++;
            }
            t.x = rectB.x;
            t.y = rectA.y;
            t.width = rectB.width;
            t.height = rectB.y - rectA.y;
            if (t.width > 0 && t.height > 0) {
                b = new Rectangle(t);
                rectCount++;
            }
            t.x = rectB.x;
            t.y = rectB.y + rectB.height;
            t.width = rectB.width;
            t.height = rectA.y + rectA.height - (rectB.y + rectB.height);
            if (t.width > 0 && t.height > 0) {
                c = new Rectangle(t);
                rectCount++;
            }
            t.x = rectB.x + rectB.width;
            t.y = rectA.y;
            t.width = rectA.x + rectA.width - (rectB.x + rectB.width);
            t.height = rectA.height;
            if (t.width > 0 && t.height > 0) {
                d = new Rectangle(t);
                rectCount++;
            }
        } else {
            if (rectB.x <= rectA.x && rectB.y <= rectA.y) {
                if ((rectB.x + rectB.width) > (rectA.x + rectA.width)) {
                    t.x = rectA.x;
                    t.y = rectB.y + rectB.height;
                    t.width = rectA.width;
                    t.height = rectA.y + rectA.height - (rectB.y + rectB.height);
                    if (t.width > 0 && t.height > 0) {
                        a = t;
                        rectCount++;
                    }
                } else if ((rectB.y + rectB.height) > (rectA.y + rectA.height)) {
                    t.setBounds((rectB.x + rectB.width), rectA.y, (rectA.x + rectA.width) - (rectB.x + rectB.width), rectA.height);
                    if (t.width > 0 && t.height > 0) {
                        a = t;
                        rectCount++;
                    }
                } else {
                    t.setBounds((rectB.x + rectB.width), rectA.y, (rectA.x + rectA.width) - (rectB.x + rectB.width), (rectB.y + rectB.height) - rectA.y);
                    if (t.width > 0 && t.height > 0) {
                        a = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds(rectA.x, (rectB.y + rectB.height), rectA.width, (rectA.y + rectA.height) - (rectB.y + rectB.height));
                    if (t.width > 0 && t.height > 0) {
                        b = new Rectangle(t);
                        rectCount++;
                    }
                }
            } else if (rectB.x <= rectA.x && (rectB.y + rectB.height) >= (rectA.y + rectA.height)) {
                if ((rectB.x + rectB.width) > (rectA.x + rectA.width)) {
                    t.setBounds(rectA.x, rectA.y, rectA.width, rectB.y - rectA.y);
                    if (t.width > 0 && t.height > 0) {
                        a = t;
                        rectCount++;
                    }
                } else {
                    t.setBounds(rectA.x, rectA.y, rectA.width, rectB.y - rectA.y);
                    if (t.width > 0 && t.height > 0) {
                        a = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds((rectB.x + rectB.width), rectB.y, (rectA.x + rectA.width) - (rectB.x + rectB.width), (rectA.y + rectA.height) - rectB.y);
                    if (t.width > 0 && t.height > 0) {
                        b = new Rectangle(t);
                        rectCount++;
                    }
                }
            } else if (rectB.x <= rectA.x) {
                if ((rectB.x + rectB.width) >= (rectA.x + rectA.width)) {
                    t.setBounds(rectA.x, rectA.y, rectA.width, rectB.y - rectA.y);
                    if (t.width > 0 && t.height > 0) {
                        a = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds(rectA.x, (rectB.y + rectB.height), rectA.width, (rectA.y + rectA.height) - (rectB.y + rectB.height));
                    if (t.width > 0 && t.height > 0) {
                        b = new Rectangle(t);
                        rectCount++;
                    }
                } else {
                    t.setBounds(rectA.x, rectA.y, rectA.width, rectB.y - rectA.y);
                    if (t.width > 0 && t.height > 0) {
                        a = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds((rectB.x + rectB.width), rectB.y, (rectA.x + rectA.width) - (rectB.x + rectB.width), rectB.height);
                    if (t.width > 0 && t.height > 0) {
                        b = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds(rectA.x, (rectB.y + rectB.height), rectA.width, (rectA.y + rectA.height) - (rectB.y + rectB.height));
                    if (t.width > 0 && t.height > 0) {
                        c = new Rectangle(t);
                        rectCount++;
                    }
                }
            } else if (rectB.x <= (rectA.x + rectA.width) && (rectB.x + rectB.width) > (rectA.x + rectA.width)) {
                if (rectB.y <= rectA.y && (rectB.y + rectB.height) > (rectA.y + rectA.height)) {
                    t.setBounds(rectA.x, rectA.y, rectB.x - rectA.x, rectA.height);
                    if (t.width > 0 && t.height > 0) {
                        a = t;
                        rectCount++;
                    }
                } else if (rectB.y <= rectA.y) {
                    t.setBounds(rectA.x, rectA.y, rectB.x - rectA.x, (rectB.y + rectB.height) - rectA.y);
                    if (t.width > 0 && t.height > 0) {
                        a = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds(rectA.x, (rectB.y + rectB.height), rectA.width, (rectA.y + rectA.height) - (rectB.y + rectB.height));
                    if (t.width > 0 && t.height > 0) {
                        b = new Rectangle(t);
                        rectCount++;
                    }
                } else if ((rectB.y + rectB.height) > (rectA.y + rectA.height)) {
                    t.setBounds(rectA.x, rectA.y, rectA.width, rectB.y - rectA.y);
                    if (t.width > 0 && t.height > 0) {
                        a = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds(rectA.x, rectB.y, rectB.x - rectA.x, (rectA.y + rectA.height) - rectB.y);
                    if (t.width > 0 && t.height > 0) {
                        b = new Rectangle(t);
                        rectCount++;
                    }
                } else {
                    t.setBounds(rectA.x, rectA.y, rectA.width, rectB.y - rectA.y);
                    if (t.width > 0 && t.height > 0) {
                        a = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds(rectA.x, rectB.y, rectB.x - rectA.x, rectB.height);
                    if (t.width > 0 && t.height > 0) {
                        b = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds(rectA.x, (rectB.y + rectB.height), rectA.width, (rectA.y + rectA.height) - (rectB.y + rectB.height));
                    if (t.width > 0 && t.height > 0) {
                        c = new Rectangle(t);
                        rectCount++;
                    }
                }
            } else if (rectB.x >= rectA.x && (rectB.x + rectB.width) <= (rectA.x + rectA.width)) {
                if (rectB.y <= rectA.y && (rectB.y + rectB.height) > (rectA.y + rectA.height)) {
                    t.setBounds(rectA.x, rectA.y, rectB.x - rectA.x, rectA.height);
                    if (t.width > 0 && t.height > 0) {
                        a = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds((rectB.x + rectB.width), rectA.y, (rectA.x + rectA.width) - (rectB.x + rectB.width), rectA.height);
                    if (t.width > 0 && t.height > 0) {
                        b = new Rectangle(t);
                        rectCount++;
                    }
                } else if (rectB.y <= rectA.y) {
                    t.setBounds(rectA.x, rectA.y, rectB.x - rectA.x, rectA.height);
                    if (t.width > 0 && t.height > 0) {
                        a = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds(rectB.x, (rectB.y + rectB.height), rectB.width, (rectA.y + rectA.height) - (rectB.y + rectB.height));
                    if (t.width > 0 && t.height > 0) {
                        b = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds((rectB.x + rectB.width), rectA.y, (rectA.x + rectA.width) - (rectB.x + rectB.width), rectA.height);
                    if (t.width > 0 && t.height > 0) {
                        c = new Rectangle(t);
                        rectCount++;
                    }
                } else {
                    t.setBounds(rectA.x, rectA.y, rectB.x - rectA.x, rectA.height);
                    if (t.width > 0 && t.height > 0) {
                        a = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds(rectB.x, rectA.y, rectB.width, rectB.y - rectA.y);
                    if (t.width > 0 && t.height > 0) {
                        b = new Rectangle(t);
                        rectCount++;
                    }
                    t.setBounds((rectB.x + rectB.width), rectA.y, (rectA.x + rectA.width) - (rectB.x + rectB.width), rectA.height);
                    if (t.width > 0 && t.height > 0) {
                        c = new Rectangle(t);
                        rectCount++;
                    }
                }
            }
        }
        result = new Rectangle[rectCount];
        rectCount = 0;
        if (a != null) result[rectCount++] = a;
        if (b != null) result[rectCount++] = b;
        if (c != null) result[rectCount++] = c;
        if (d != null) result[rectCount++] = d;
        return result;
    }
    
    public static boolean isLeftMouseButton(MouseEvent anEvent) {
        return ((anEvent.getModifiers() & InputEvent.BUTTON1_MASK) != 0);
    }
    
    public static boolean isMiddleMouseButton(MouseEvent anEvent) {
        return ((anEvent.getModifiers() & InputEvent.BUTTON2_MASK) == InputEvent.BUTTON2_MASK);
    }
    
    public static boolean isRightMouseButton(MouseEvent anEvent) {
        return ((anEvent.getModifiers() & InputEvent.BUTTON3_MASK) == InputEvent.BUTTON3_MASK);
    }
    
    public static int computeStringWidth(FontMetrics fm, String str) {
        return SwingUtilities2.stringWidth(null, fm, str);
    }
    
    public static String layoutCompoundLabel(JComponent c, FontMetrics fm, String text, Icon icon, int verticalAlignment, int horizontalAlignment, int verticalTextPosition, int horizontalTextPosition, Rectangle viewR, Rectangle iconR, Rectangle textR, int textIconGap) {
        boolean orientationIsLeftToRight = true;
        int hAlign = horizontalAlignment;
        int hTextPos = horizontalTextPosition;
        if (c != null) {
            if (!(c.getComponentOrientation().isLeftToRight())) {
                orientationIsLeftToRight = false;
            }
        }
        switch (horizontalAlignment) {
        case LEADING: 
            hAlign = (orientationIsLeftToRight) ? LEFT : RIGHT;
            break;
        
        case TRAILING: 
            hAlign = (orientationIsLeftToRight) ? RIGHT : LEFT;
            break;
        
        }
        switch (horizontalTextPosition) {
        case LEADING: 
            hTextPos = (orientationIsLeftToRight) ? LEFT : RIGHT;
            break;
        
        case TRAILING: 
            hTextPos = (orientationIsLeftToRight) ? RIGHT : LEFT;
            break;
        
        }
        return layoutCompoundLabelImpl(c, fm, text, icon, verticalAlignment, hAlign, verticalTextPosition, hTextPos, viewR, iconR, textR, textIconGap);
    }
    
    public static String layoutCompoundLabel(FontMetrics fm, String text, Icon icon, int verticalAlignment, int horizontalAlignment, int verticalTextPosition, int horizontalTextPosition, Rectangle viewR, Rectangle iconR, Rectangle textR, int textIconGap) {
        return layoutCompoundLabelImpl(null, fm, text, icon, verticalAlignment, horizontalAlignment, verticalTextPosition, horizontalTextPosition, viewR, iconR, textR, textIconGap);
    }
    
    private static String layoutCompoundLabelImpl(JComponent c, FontMetrics fm, String text, Icon icon, int verticalAlignment, int horizontalAlignment, int verticalTextPosition, int horizontalTextPosition, Rectangle viewR, Rectangle iconR, Rectangle textR, int textIconGap) {
        if (icon != null) {
            iconR.width = icon.getIconWidth();
            iconR.height = icon.getIconHeight();
        } else {
            iconR.width = iconR.height = 0;
        }
        boolean textIsEmpty = (text == null) || text.equals("");
        int lsb = 0;
        int gap;
        View v = null;
        if (textIsEmpty) {
            textR.width = textR.height = 0;
            text = "";
            gap = 0;
        } else {
            int availTextWidth;
            gap = (icon == null) ? 0 : textIconGap;
            if (horizontalTextPosition == CENTER) {
                availTextWidth = viewR.width;
            } else {
                availTextWidth = viewR.width - (iconR.width + gap);
            }
            v = (c != null) ? (View)(View)c.getClientProperty("html") : null;
            if (v != null) {
                textR.width = Math.min(availTextWidth, (int)v.getPreferredSpan(View.X_AXIS));
                textR.height = (int)v.getPreferredSpan(View.Y_AXIS);
            } else {
                textR.width = SwingUtilities2.stringWidth(c, fm, text);
                lsb = SwingUtilities2.getLeftSideBearing(c, fm, text);
                if (lsb < 0) {
                    textR.width -= lsb;
                }
                if (textR.width > availTextWidth) {
                    text = SwingUtilities2.clipString(c, fm, text, availTextWidth);
                    textR.width = SwingUtilities2.stringWidth(c, fm, text);
                }
                textR.height = fm.getHeight();
            }
        }
        if (verticalTextPosition == TOP) {
            if (horizontalTextPosition != CENTER) {
                textR.y = 0;
            } else {
                textR.y = -(textR.height + gap);
            }
        } else if (verticalTextPosition == CENTER) {
            textR.y = (iconR.height / 2) - (textR.height / 2);
        } else {
            if (horizontalTextPosition != CENTER) {
                textR.y = iconR.height - textR.height;
            } else {
                textR.y = (iconR.height + gap);
            }
        }
        if (horizontalTextPosition == LEFT) {
            textR.x = -(textR.width + gap);
        } else if (horizontalTextPosition == CENTER) {
            textR.x = (iconR.width / 2) - (textR.width / 2);
        } else {
            textR.x = (iconR.width + gap);
        }
        int labelR_x = Math.min(iconR.x, textR.x);
        int labelR_width = Math.max(iconR.x + iconR.width, textR.x + textR.width) - labelR_x;
        int labelR_y = Math.min(iconR.y, textR.y);
        int labelR_height = Math.max(iconR.y + iconR.height, textR.y + textR.height) - labelR_y;
        int dx;
        int dy;
        if (verticalAlignment == TOP) {
            dy = viewR.y - labelR_y;
        } else if (verticalAlignment == CENTER) {
            dy = (viewR.y + (viewR.height / 2)) - (labelR_y + (labelR_height / 2));
        } else {
            dy = (viewR.y + viewR.height) - (labelR_y + labelR_height);
        }
        if (horizontalAlignment == LEFT) {
            dx = viewR.x - labelR_x;
        } else if (horizontalAlignment == RIGHT) {
            dx = (viewR.x + viewR.width) - (labelR_x + labelR_width);
        } else {
            dx = (viewR.x + (viewR.width / 2)) - (labelR_x + (labelR_width / 2));
        }
        textR.x += dx;
        textR.y += dy;
        iconR.x += dx;
        iconR.y += dy;
        if (lsb < 0) {
            textR.x -= lsb;
        }
        return text;
    }
    
    public static void paintComponent(Graphics g, Component c, Container p, int x, int y, int w, int h) {
        getCellRendererPane(c, p).paintComponent(g, c, p, x, y, w, h, false);
    }
    
    public static void paintComponent(Graphics g, Component c, Container p, Rectangle r) {
        paintComponent(g, c, p, r.x, r.y, r.width, r.height);
    }
    
    private static CellRendererPane getCellRendererPane(Component c, Container p) {
        Container shell = c.getParent();
        if (shell instanceof CellRendererPane) {
            if (shell.getParent() != p) {
                p.add(shell);
            }
        } else {
            shell = new CellRendererPane();
            shell.add(c);
            p.add(shell);
        }
        return (CellRendererPane)(CellRendererPane)shell;
    }
    
    public static void updateComponentTreeUI(Component c) {
        updateComponentTreeUI0(c);
        c.invalidate();
        c.validate();
        c.repaint();
    }
    
    private static void updateComponentTreeUI0(Component c) {
        if (c instanceof JComponent) {
            ((JComponent)(JComponent)c).updateUI();
        }
        Component[] children = null;
        if (c instanceof JMenu) {
            children = ((JMenu)(JMenu)c).getMenuComponents();
        } else if (c instanceof Container) {
            children = ((Container)(Container)c).getComponents();
        }
        if (children != null) {
            for (int i = 0; i < children.length; i++) {
                updateComponentTreeUI0(children[i]);
            }
        }
    }
    
    public static void invokeLater(Runnable doRun) {
        EventQueue.invokeLater(doRun);
    }
    
    public static void invokeAndWait(final Runnable doRun) throws InterruptedException, InvocationTargetException {
        EventQueue.invokeAndWait(doRun);
    }
    
    public static boolean isEventDispatchThread() {
        return EventQueue.isDispatchThread();
    }
    
    public static int getAccessibleIndexInParent(Component c) {
        return c.getAccessibleContext().getAccessibleIndexInParent();
    }
    
    public static Accessible getAccessibleAt(Component c, Point p) {
        if (c instanceof Container) {
            return c.getAccessibleContext().getAccessibleComponent().getAccessibleAt(p);
        } else if (c instanceof Accessible) {
            Accessible a = (Accessible)(Accessible)c;
            if (a != null) {
                AccessibleContext ac = a.getAccessibleContext();
                if (ac != null) {
                    AccessibleComponent acmp;
                    Point location;
                    int nchildren = ac.getAccessibleChildrenCount();
                    for (int i = 0; i < nchildren; i++) {
                        a = ac.getAccessibleChild(i);
                        if (a != null) {
                            ac = a.getAccessibleContext();
                            if (ac != null) {
                                acmp = ac.getAccessibleComponent();
                                if ((acmp != null) && (acmp.isShowing())) {
                                    location = acmp.getLocation();
                                    Point np = new Point(p.x - location.x, p.y - location.y);
                                    if (acmp.contains(np)) {
                                        return a;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            return (Accessible)(Accessible)c;
        }
        return null;
    }
    
    public static AccessibleStateSet getAccessibleStateSet(Component c) {
        return c.getAccessibleContext().getAccessibleStateSet();
    }
    
    public static int getAccessibleChildrenCount(Component c) {
        return c.getAccessibleContext().getAccessibleChildrenCount();
    }
    
    public static Accessible getAccessibleChild(Component c, int i) {
        return c.getAccessibleContext().getAccessibleChild(i);
    }
    
    
    public static Component findFocusOwner(Component c) {
        Component focusOwner = KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusOwner();
        for (Component temp = focusOwner; temp != null; temp = (temp instanceof Window) ? null : temp.getParent()) {
            if (temp == c) {
                return focusOwner;
            }
        }
        return null;
    }
    
    public static JRootPane getRootPane(Component c) {
        if (c instanceof RootPaneContainer) {
            return ((RootPaneContainer)(RootPaneContainer)c).getRootPane();
        }
        for (; c != null; c = c.getParent()) {
            if (c instanceof JRootPane) {
                return (JRootPane)(JRootPane)c;
            }
        }
        return null;
    }
    
    public static Component getRoot(Component c) {
        Component applet = null;
        for (Component p = c; p != null; p = p.getParent()) {
            if (p instanceof Window) {
                return p;
            }
            if (p instanceof Applet) {
                applet = p;
            }
        }
        return applet;
    }
    
    public static boolean processKeyBindings(KeyEvent event) {
        if (event != null) {
            if (event.isConsumed()) {
                return false;
            }
            Component component = event.getComponent();
            Component last = component;
            boolean pressed = (event.getID() == KeyEvent.KEY_PRESSED);
            if (!isValidKeyEventForKeyBindings(event)) {
                return false;
            }
            while (component != null) {
                if (component instanceof JComponent) {
                    return ((JComponent)(JComponent)component).processKeyBindings(event, pressed);
                }
                last = component;
                component = component.getParent();
            }
            if ((last instanceof Applet) || (last instanceof Window)) {
                return JComponent.processKeyBindingsForAllComponents(event, (Container)(Container)last, pressed);
            }
        }
        return false;
    }
    
    static boolean isValidKeyEventForKeyBindings(KeyEvent e) {
        if (e.getID() == KeyEvent.KEY_TYPED) {
            int mod = e.getModifiers();
            if (((mod & ActionEvent.ALT_MASK) != 0) && ((mod & ActionEvent.CTRL_MASK) == 0)) {
                return false;
            }
        }
        return true;
    }
    
    public static boolean notifyAction(Action action, KeyStroke ks, KeyEvent event, Object sender, int modifiers) {
        if (action == null) {
            return false;
        }
        if (action instanceof UIAction) {
            if (!((UIAction)(UIAction)action).isEnabled(sender)) {
                return false;
            }
        } else if (!action.isEnabled()) {
            return false;
        }
        Object commandO;
        boolean stayNull;
        commandO = action.getValue(Action.ACTION_COMMAND_KEY);
        if (commandO == null && (action instanceof JComponent$ActionStandin)) {
            stayNull = true;
        } else {
            stayNull = false;
        }
        String command;
        if (commandO != null) {
            command = commandO.toString();
        } else if (!stayNull && event.getKeyChar() != KeyEvent.CHAR_UNDEFINED) {
            command = String.valueOf(event.getKeyChar());
        } else {
            command = null;
        }
        action.actionPerformed(new ActionEvent(sender, ActionEvent.ACTION_PERFORMED, command, event.getWhen(), modifiers));
        return true;
    }
    
    public static void replaceUIInputMap(JComponent component, int type, InputMap uiInputMap) {
        InputMap map = component.getInputMap(type, (uiInputMap != null));
        while (map != null) {
            InputMap parent = map.getParent();
            if (parent == null || (parent instanceof UIResource)) {
                map.setParent(uiInputMap);
                return;
            }
            map = parent;
        }
    }
    
    public static void replaceUIActionMap(JComponent component, ActionMap uiActionMap) {
        ActionMap map = component.getActionMap((uiActionMap != null));
        ;
        while (map != null) {
            ActionMap parent = map.getParent();
            if (parent == null || (parent instanceof UIResource)) {
                map.setParent(uiActionMap);
                return;
            }
            map = parent;
        }
    }
    
    public static InputMap getUIInputMap(JComponent component, int condition) {
        InputMap map = component.getInputMap(condition, false);
        while (map != null) {
            InputMap parent = map.getParent();
            if (parent instanceof UIResource) {
                return parent;
            }
            map = parent;
        }
        return null;
    }
    
    public static ActionMap getUIActionMap(JComponent component) {
        ActionMap map = component.getActionMap(false);
        while (map != null) {
            ActionMap parent = map.getParent();
            if (parent instanceof UIResource) {
                return parent;
            }
            map = parent;
        }
        return null;
    }
    private static final Object sharedOwnerFrameKey = new StringBuffer("SwingUtilities.sharedOwnerFrame");
    {
    }
    
    static Frame getSharedOwnerFrame() throws HeadlessException {
        Frame sharedOwnerFrame = (Frame)(Frame)SwingUtilities.appContextGet(sharedOwnerFrameKey);
        if (sharedOwnerFrame == null) {
            sharedOwnerFrame = new SwingUtilities$SharedOwnerFrame();
            SwingUtilities.appContextPut(sharedOwnerFrameKey, sharedOwnerFrame);
        }
        return sharedOwnerFrame;
    }
    
    static WindowListener getSharedOwnerFrameShutdownListener() throws HeadlessException {
        Frame sharedOwnerFrame = getSharedOwnerFrame();
        return (WindowListener)(WindowListener)sharedOwnerFrame;
    }
    
    static Object appContextGet(Object key) {
        return AppContext.getAppContext().get(key);
    }
    
    static void appContextPut(Object key, Object value) {
        AppContext.getAppContext().put(key, value);
    }
    
    static void appContextRemove(Object key) {
        AppContext.getAppContext().remove(key);
    }
    
    static Class loadSystemClass(String className) throws ClassNotFoundException {
        return Class.forName(className, true, Thread.currentThread().getContextClassLoader());
    }
    
    static boolean isLeftToRight(Component c) {
        return c.getComponentOrientation().isLeftToRight();
    }
    
    private SwingUtilities() {
        
        throw new Error("SwingUtilities is just a container for static methods");
    }
    
    static boolean doesIconReferenceImage(Icon icon, Image image) {
        Image iconImage = (icon != null && (icon instanceof ImageIcon)) ? ((ImageIcon)(ImageIcon)icon).getImage() : null;
        return (iconImage == image);
    }
    
    static int findDisplayedMnemonicIndex(String text, int mnemonic) {
        if (text == null || mnemonic == '\000') {
            return -1;
        }
        char uc = Character.toUpperCase((char)mnemonic);
        char lc = Character.toLowerCase((char)mnemonic);
        int uci = text.indexOf(uc);
        int lci = text.indexOf(lc);
        if (uci == -1) {
            return lci;
        } else if (lci == -1) {
            return uci;
        } else {
            return (lci < uci) ? lci : uci;
        }
    }
    
    public static Rectangle calculateInnerArea(JComponent c, Rectangle r) {
        if (c == null) {
            return null;
        }
        Rectangle rect = r;
        Insets insets = c.getInsets();
        if (rect == null) {
            rect = new Rectangle();
        }
        rect.x = insets.left;
        rect.y = insets.top;
        rect.width = c.getWidth() - insets.left - insets.right;
        rect.height = c.getHeight() - insets.top - insets.bottom;
        return rect;
    }
}
