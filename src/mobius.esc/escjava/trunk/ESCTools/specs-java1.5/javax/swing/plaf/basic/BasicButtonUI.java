package javax.swing.plaf.basic;

import com.sun.java.swing.SwingUtilities2;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.border.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.plaf.ButtonUI;
import javax.swing.plaf.UIResource;
import javax.swing.plaf.ComponentUI;
import javax.swing.text.View;

public class BasicButtonUI extends ButtonUI {
    
    public BasicButtonUI() {
        
    }
    private static final BasicButtonUI buttonUI = new BasicButtonUI();
    protected int defaultTextIconGap;
    private int shiftOffset = 0;
    protected int defaultTextShiftOffset;
    private static final String propertyPrefix = "Button.";
    
    public static ComponentUI createUI(JComponent c) {
        return buttonUI;
    }
    
    protected String getPropertyPrefix() {
        return propertyPrefix;
    }
    
    public void installUI(JComponent c) {
        installDefaults((AbstractButton)(AbstractButton)c);
        installListeners((AbstractButton)(AbstractButton)c);
        installKeyboardActions((AbstractButton)(AbstractButton)c);
        BasicHTML.updateRenderer(c, ((AbstractButton)(AbstractButton)c).getText());
    }
    
    protected void installDefaults(AbstractButton b) {
        String pp = getPropertyPrefix();
        defaultTextShiftOffset = UIManager.getInt(pp + "textShiftOffset");
        if (b.isContentAreaFilled()) {
            LookAndFeel.installProperty(b, "opaque", Boolean.TRUE);
        } else {
            LookAndFeel.installProperty(b, "opaque", Boolean.FALSE);
        }
        if (b.getMargin() == null || (b.getMargin() instanceof UIResource)) {
            b.setMargin(UIManager.getInsets(pp + "margin"));
        }
        LookAndFeel.installColorsAndFont(b, pp + "background", pp + "foreground", pp + "font");
        LookAndFeel.installBorder(b, pp + "border");
        Object rollover = UIManager.get(pp + "rollover");
        if (rollover != null) {
            LookAndFeel.installProperty(b, "rolloverEnabled", rollover);
        }
    }
    
    protected void installListeners(AbstractButton b) {
        BasicButtonListener listener = createButtonListener(b);
        if (listener != null) {
            b.addMouseListener(listener);
            b.addMouseMotionListener(listener);
            b.addFocusListener(listener);
            b.addPropertyChangeListener(listener);
            b.addChangeListener(listener);
        }
    }
    
    protected void installKeyboardActions(AbstractButton b) {
        BasicButtonListener listener = getButtonListener(b);
        if (listener != null) {
            listener.installKeyboardActions(b);
        }
    }
    
    public void uninstallUI(JComponent c) {
        uninstallKeyboardActions((AbstractButton)(AbstractButton)c);
        uninstallListeners((AbstractButton)(AbstractButton)c);
        uninstallDefaults((AbstractButton)(AbstractButton)c);
        BasicHTML.updateRenderer(c, "");
    }
    
    protected void uninstallKeyboardActions(AbstractButton b) {
        BasicButtonListener listener = getButtonListener(b);
        if (listener != null) {
            listener.uninstallKeyboardActions(b);
        }
    }
    
    protected void uninstallListeners(AbstractButton b) {
        BasicButtonListener listener = getButtonListener(b);
        if (listener != null) {
            b.removeMouseListener(listener);
            b.removeMouseListener(listener);
            b.removeMouseMotionListener(listener);
            b.removeFocusListener(listener);
            b.removeChangeListener(listener);
            b.removePropertyChangeListener(listener);
        }
    }
    
    protected void uninstallDefaults(AbstractButton b) {
        LookAndFeel.uninstallBorder(b);
    }
    
    protected BasicButtonListener createButtonListener(AbstractButton b) {
        return new BasicButtonListener(b);
    }
    
    public int getDefaultTextIconGap(AbstractButton b) {
        return defaultTextIconGap;
    }
    private static Rectangle viewRect = new Rectangle();
    private static Rectangle textRect = new Rectangle();
    private static Rectangle iconRect = new Rectangle();
    
    public void paint(Graphics g, JComponent c) {
        AbstractButton b = (AbstractButton)(AbstractButton)c;
        ButtonModel model = b.getModel();
        FontMetrics fm = SwingUtilities2.getFontMetrics(b, g);
        Insets i = c.getInsets();
        viewRect.x = i.left;
        viewRect.y = i.top;
        viewRect.width = b.getWidth() - (i.right + viewRect.x);
        viewRect.height = b.getHeight() - (i.bottom + viewRect.y);
        textRect.x = textRect.y = textRect.width = textRect.height = 0;
        iconRect.x = iconRect.y = iconRect.width = iconRect.height = 0;
        Font f = c.getFont();
        g.setFont(f);
        String text = SwingUtilities.layoutCompoundLabel(c, fm, b.getText(), b.getIcon(), b.getVerticalAlignment(), b.getHorizontalAlignment(), b.getVerticalTextPosition(), b.getHorizontalTextPosition(), viewRect, iconRect, textRect, b.getText() == null ? 0 : b.getIconTextGap());
        clearTextShiftOffset();
        if (model.isArmed() && model.isPressed()) {
            paintButtonPressed(g, b);
        }
        if (b.getIcon() != null) {
            paintIcon(g, c, iconRect);
        }
        if (text != null && !text.equals("")) {
            View v = (View)(View)c.getClientProperty(BasicHTML.propertyKey);
            if (v != null) {
                v.paint(g, textRect);
            } else {
                paintText(g, b, textRect, text);
            }
        }
        if (b.isFocusPainted() && b.hasFocus()) {
            paintFocus(g, b, viewRect, textRect, iconRect);
        }
    }
    
    protected void paintIcon(Graphics g, JComponent c, Rectangle iconRect) {
        AbstractButton b = (AbstractButton)(AbstractButton)c;
        ButtonModel model = b.getModel();
        Icon icon = b.getIcon();
        Icon tmpIcon = null;
        if (icon == null) {
            return;
        }
        if (!model.isEnabled()) {
            if (model.isSelected()) {
                tmpIcon = (Icon)b.getDisabledSelectedIcon();
            } else {
                tmpIcon = (Icon)b.getDisabledIcon();
            }
        } else if (model.isPressed() && model.isArmed()) {
            tmpIcon = (Icon)b.getPressedIcon();
            if (tmpIcon != null) {
                clearTextShiftOffset();
            }
        } else if (b.isRolloverEnabled() && model.isRollover()) {
            if (model.isSelected()) {
                tmpIcon = (Icon)b.getRolloverSelectedIcon();
            } else {
                tmpIcon = (Icon)b.getRolloverIcon();
            }
        } else if (model.isSelected()) {
            tmpIcon = (Icon)b.getSelectedIcon();
        }
        if (tmpIcon != null) {
            icon = tmpIcon;
        }
        if (model.isPressed() && model.isArmed()) {
            icon.paintIcon(c, g, iconRect.x + getTextShiftOffset(), iconRect.y + getTextShiftOffset());
        } else {
            icon.paintIcon(c, g, iconRect.x, iconRect.y);
        }
    }
    
    protected void paintText(Graphics g, JComponent c, Rectangle textRect, String text) {
        AbstractButton b = (AbstractButton)(AbstractButton)c;
        ButtonModel model = b.getModel();
        FontMetrics fm = SwingUtilities2.getFontMetrics(c, g);
        int mnemonicIndex = b.getDisplayedMnemonicIndex();
        if (model.isEnabled()) {
            g.setColor(b.getForeground());
            SwingUtilities2.drawStringUnderlineCharAt(c, g, text, mnemonicIndex, textRect.x + getTextShiftOffset(), textRect.y + fm.getAscent() + getTextShiftOffset());
        } else {
            g.setColor(b.getBackground().brighter());
            SwingUtilities2.drawStringUnderlineCharAt(c, g, text, mnemonicIndex, textRect.x, textRect.y + fm.getAscent());
            g.setColor(b.getBackground().darker());
            SwingUtilities2.drawStringUnderlineCharAt(c, g, text, mnemonicIndex, textRect.x - 1, textRect.y + fm.getAscent() - 1);
        }
    }
    
    protected void paintText(Graphics g, AbstractButton b, Rectangle textRect, String text) {
        paintText(g, (JComponent)b, textRect, text);
    }
    
    protected void paintFocus(Graphics g, AbstractButton b, Rectangle viewRect, Rectangle textRect, Rectangle iconRect) {
    }
    
    protected void paintButtonPressed(Graphics g, AbstractButton b) {
    }
    
    protected void clearTextShiftOffset() {
        this.shiftOffset = 0;
    }
    
    protected void setTextShiftOffset() {
        this.shiftOffset = defaultTextShiftOffset;
    }
    
    protected int getTextShiftOffset() {
        return shiftOffset;
    }
    
    public Dimension getMinimumSize(JComponent c) {
        Dimension d = getPreferredSize(c);
        View v = (View)(View)c.getClientProperty(BasicHTML.propertyKey);
        if (v != null) {
            d.width -= v.getPreferredSpan(View.X_AXIS) - v.getMinimumSpan(View.X_AXIS);
        }
        return d;
    }
    
    public Dimension getPreferredSize(JComponent c) {
        AbstractButton b = (AbstractButton)(AbstractButton)c;
        return BasicGraphicsUtils.getPreferredButtonSize(b, b.getIconTextGap());
    }
    
    public Dimension getMaximumSize(JComponent c) {
        Dimension d = getPreferredSize(c);
        View v = (View)(View)c.getClientProperty(BasicHTML.propertyKey);
        if (v != null) {
            d.width += v.getMaximumSpan(View.X_AXIS) - v.getPreferredSpan(View.X_AXIS);
        }
        return d;
    }
    
    private BasicButtonListener getButtonListener(AbstractButton b) {
        MouseMotionListener[] listeners = b.getMouseMotionListeners();
        if (listeners != null) {
            for (int counter = 0; counter < listeners.length; counter++) {
                if (listeners[counter] instanceof BasicButtonListener) {
                    return (BasicButtonListener)(BasicButtonListener)listeners[counter];
                }
            }
        }
        return null;
    }
}
