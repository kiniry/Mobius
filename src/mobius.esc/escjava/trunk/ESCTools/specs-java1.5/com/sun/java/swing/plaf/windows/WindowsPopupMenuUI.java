package com.sun.java.swing.plaf.windows;

import java.awt.Graphics;
import java.awt.Insets;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import com.sun.java.swing.plaf.windows.TMSchema.Part;
import com.sun.java.swing.plaf.windows.TMSchema.State;
import com.sun.java.swing.plaf.windows.XPStyle.Skin;

public class WindowsPopupMenuUI extends BasicPopupMenuUI {
    
    public WindowsPopupMenuUI() {
        
    }
    static WindowsPopupMenuUI$MnemonicListener mnemonicListener = null;
    static final Object GUTTER_OFFSET_KEY = new StringBuilder("GUTTER_OFFSET_KEY");
    
    public static ComponentUI createUI(JComponent c) {
        return new WindowsPopupMenuUI();
    }
    
    public void installListeners() {
        super.installListeners();
        if (!UIManager.getBoolean("Button.showMnemonics") && mnemonicListener == null) {
            mnemonicListener = new WindowsPopupMenuUI$MnemonicListener();
            MenuSelectionManager.defaultManager().addChangeListener(mnemonicListener);
        }
    }
    
    public Popup getPopup(JPopupMenu popupMenu, int x, int y) {
        PopupFactory popupFactory = PopupFactory.getSharedInstance();
        return popupFactory.getPopup(popupMenu.getInvoker(), popupMenu, x, y);
    }
    {
    }
    
    static int getTextOffset(JComponent c) {
        int rv = -1;
        return rv;
    }
    
    static int getSpanBeforeGutter() {
        return 3;
    }
    
    static int getSpanAfterGutter() {
        return 3;
    }
    
    static int getGutterWidth() {
        int rv = 2;
        XPStyle xp = XPStyle.getXP();
        if (xp != null) {
            XPStyle$Skin skin = xp.getSkin(null, TMSchema$Part.MP_POPUPGUTTER);
            rv = skin.getWidth();
        }
        return rv;
    }
    
    private static boolean isLeftToRight(JComponent c) {
        boolean leftToRight = true;
        for (int i = c.getComponentCount() - 1; i >= 0 && leftToRight; i--) {
            leftToRight = c.getComponent(i).getComponentOrientation().isLeftToRight();
        }
        return leftToRight;
    }
    
    @Override()
    public void paint(Graphics g, JComponent c) {
        if (WindowsMenuItemUI.isVistaPainting()) {
            XPStyle xp = XPStyle.getXP();
            XPStyle$Skin skin = xp.getSkin(c, TMSchema$Part.MP_POPUPBACKGROUND);
            skin.paintSkin(g, 0, 0, c.getWidth(), c.getHeight(), TMSchema$State.NORMAL);
            int textOffset = getTextOffset(c);
            if (textOffset >= 0 && isLeftToRight(c)) {
                skin = xp.getSkin(c, TMSchema$Part.MP_POPUPGUTTER);
                int gutterWidth = getGutterWidth();
                int gutterOffset = textOffset - getSpanAfterGutter() - gutterWidth;
                c.putClientProperty(GUTTER_OFFSET_KEY, Integer.valueOf(gutterOffset));
                Insets insets = c.getInsets();
                skin.paintSkin(g, gutterOffset, insets.top, gutterWidth, c.getHeight() - insets.bottom - insets.top, TMSchema$State.NORMAL);
            } else {
                if (c.getClientProperty(GUTTER_OFFSET_KEY) != null) {
                    c.putClientProperty(GUTTER_OFFSET_KEY, null);
                }
            }
        } else {
            super.paint(g, c);
        }
    }
}
