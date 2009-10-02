package com.sun.java.swing.plaf.windows;

import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import javax.swing.*;
import java.awt.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.XPStyle.Skin;

public class WindowsButtonUI extends BasicButtonUI {
    
    public WindowsButtonUI() {
        
    }
    private static final WindowsButtonUI windowsButtonUI = new WindowsButtonUI();
    protected int dashedRectGapX;
    protected int dashedRectGapY;
    protected int dashedRectGapWidth;
    protected int dashedRectGapHeight;
    protected Color focusColor;
    private boolean defaults_initialized = false;
    
    public static ComponentUI createUI(JComponent c) {
        return windowsButtonUI;
    }
    
    protected void installDefaults(AbstractButton b) {
        super.installDefaults(b);
        if (!defaults_initialized) {
            String pp = getPropertyPrefix();
            dashedRectGapX = UIManager.getInt(pp + "dashedRectGapX");
            dashedRectGapY = UIManager.getInt(pp + "dashedRectGapY");
            dashedRectGapWidth = UIManager.getInt(pp + "dashedRectGapWidth");
            dashedRectGapHeight = UIManager.getInt(pp + "dashedRectGapHeight");
            focusColor = UIManager.getColor(pp + "focus");
            defaults_initialized = true;
        }
        XPStyle xp = XPStyle.getXP();
        if (xp != null) {
            b.setBorder(xp.getBorder(b, getXPButtonType(b)));
            LookAndFeel.installProperty(b, "rolloverEnabled", Boolean.TRUE);
        }
    }
    
    protected void uninstallDefaults(AbstractButton b) {
        super.uninstallDefaults(b);
        defaults_initialized = false;
    }
    
    protected Color getFocusColor() {
        return focusColor;
    }
    
    protected void paintText(Graphics g, AbstractButton b, Rectangle textRect, String text) {
        WindowsGraphicsUtils.paintText(g, b, textRect, text, getTextShiftOffset());
    }
    
    protected void paintFocus(Graphics g, AbstractButton b, Rectangle viewRect, Rectangle textRect, Rectangle iconRect) {
        if (b.getParent() instanceof JToolBar) {
            return;
        }
        if (XPStyle.getXP() != null) {
            return;
        }
        int width = b.getWidth();
        int height = b.getHeight();
        g.setColor(getFocusColor());
        BasicGraphicsUtils.drawDashedRect(g, dashedRectGapX, dashedRectGapY, width - dashedRectGapWidth, height - dashedRectGapHeight);
    }
    
    protected void paintButtonPressed(Graphics g, AbstractButton b) {
        setTextShiftOffset();
    }
    
    public Dimension getPreferredSize(JComponent c) {
        Dimension d = super.getPreferredSize(c);
        AbstractButton b = (AbstractButton)(AbstractButton)c;
        if (d != null && b.isFocusPainted()) {
            if (d.width % 2 == 0) {
                d.width += 1;
            }
            if (d.height % 2 == 0) {
                d.height += 1;
            }
        }
        return d;
    }
    private static Rectangle viewRect = new Rectangle();
    
    public void paint(Graphics g, JComponent c) {
        if (XPStyle.getXP() != null) {
            WindowsButtonUI.paintXPButtonBackground(g, c);
        }
        super.paint(g, c);
    }
    
    static TMSchema$Part getXPButtonType(AbstractButton b) {
        boolean toolbar = (b.getParent() instanceof JToolBar);
        return toolbar ? TMSchema$Part.TP_BUTTON : TMSchema$Part.BP_PUSHBUTTON;
    }
    
    static void paintXPButtonBackground(Graphics g, JComponent c) {
        AbstractButton b = (AbstractButton)(AbstractButton)c;
        XPStyle xp = XPStyle.getXP();
        boolean toolbar = (b.getParent() instanceof JToolBar);
        TMSchema$Part part = getXPButtonType(b);
        if (b.isContentAreaFilled() && xp != null) {
            ButtonModel model = b.getModel();
            XPStyle$Skin skin = xp.getSkin(b, part);
            TMSchema$State state = TMSchema$State.NORMAL;
            if (toolbar) {
                if (model.isArmed() && model.isPressed()) {
                    state = TMSchema$State.PRESSED;
                } else if (!model.isEnabled()) {
                    state = TMSchema$State.DISABLED;
                } else if (model.isSelected() && model.isRollover()) {
                    state = TMSchema$State.HOTCHECKED;
                } else if (model.isSelected()) {
                    state = TMSchema$State.CHECKED;
                } else if (model.isRollover()) {
                    state = TMSchema$State.HOT;
                }
            } else {
                if (model.isArmed() && model.isPressed() || model.isSelected()) {
                    state = TMSchema$State.PRESSED;
                } else if (!model.isEnabled()) {
                    state = TMSchema$State.DISABLED;
                } else if (model.isRollover() || model.isPressed()) {
                    state = TMSchema$State.HOT;
                } else if (b instanceof JButton && ((JButton)(JButton)b).isDefaultButton()) {
                    state = TMSchema$State.DEFAULTED;
                } else if (c.hasFocus()) {
                    state = TMSchema$State.HOT;
                }
            }
            Dimension d = c.getSize();
            int dx = 0;
            int dy = 0;
            int dw = d.width;
            int dh = d.height;
            Border border = c.getBorder();
            Insets insets;
            if (border != null) {
                insets = WindowsButtonUI.getOpaqueInsets(border, c);
            } else {
                insets = c.getInsets();
            }
            if (insets != null) {
                dx += insets.left;
                dy += insets.top;
                dw -= (insets.left + insets.right);
                dh -= (insets.top + insets.bottom);
            }
            skin.paintSkin(g, dx, dy, dw, dh, state);
        }
    }
    
    private static Insets getOpaqueInsets(Border b, Component c) {
        if (b == null) {
            return null;
        }
        if (b.isBorderOpaque()) {
            return b.getBorderInsets(c);
        } else if (b instanceof CompoundBorder) {
            CompoundBorder cb = (CompoundBorder)(CompoundBorder)b;
            Insets iOut = getOpaqueInsets(cb.getOutsideBorder(), c);
            if (iOut != null && iOut.equals(cb.getOutsideBorder().getBorderInsets(c))) {
                Insets iIn = getOpaqueInsets(cb.getInsideBorder(), c);
                if (iIn == null) {
                    return iOut;
                } else {
                    return new Insets(iOut.top + iIn.top, iOut.left + iIn.left, iOut.bottom + iIn.bottom, iOut.right + iIn.right);
                }
            } else {
                return iOut;
            }
        } else {
            return null;
        }
    }
}
