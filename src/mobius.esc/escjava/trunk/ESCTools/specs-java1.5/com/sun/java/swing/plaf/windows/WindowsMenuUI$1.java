package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.*;
import com.sun.java.swing.plaf.windows.TMSchema.Part;
import com.sun.java.swing.plaf.windows.TMSchema.State;

class WindowsMenuUI$1 implements WindowsMenuItemUIAccessor {
    /*synthetic*/ final WindowsMenuUI this$0;
    
    WindowsMenuUI$1(/*synthetic*/ final WindowsMenuUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public JMenuItem getMenuItem() {
        return WindowsMenuUI.access$000(this$0);
    }
    
    public TMSchema$State getState(JMenuItem menu) {
        TMSchema$State state = menu.isEnabled() ? TMSchema$State.NORMAL : TMSchema$State.DISABLED;
        ButtonModel model = menu.getModel();
        if (model.isArmed() || model.isSelected()) {
            state = (menu.isEnabled()) ? TMSchema$State.PUSHED : TMSchema$State.DISABLEDPUSHED;
        } else if (model.isRollover() && ((JMenu)(JMenu)menu).isTopLevelMenu()) {
            TMSchema$State stateTmp = state;
            state = (menu.isEnabled()) ? TMSchema$State.HOT : TMSchema$State.DISABLEDHOT;
            for (MenuElement[] arr$ = ((JMenuBar)(JMenuBar)menu.getParent()).getSubElements(), len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
                MenuElement menuElement = arr$[i$];
                {
                    if (((JMenuItem)(JMenuItem)menuElement).isSelected()) {
                        state = stateTmp;
                        break;
                    }
                }
            }
        }
        if (!((JMenu)(JMenu)menu).isTopLevelMenu()) {
            if (state == TMSchema$State.PUSHED) {
                state = TMSchema$State.HOT;
            } else if (state == TMSchema$State.DISABLEDPUSHED) {
                state = TMSchema$State.DISABLEDHOT;
            }
        }
        if (((JMenu)(JMenu)menu).isTopLevelMenu() && WindowsMenuItemUI.isVistaPainting()) {
            if (!WindowsMenuBarUI.isActive(menu)) {
                state = TMSchema$State.DISABLED;
            }
        }
        return state;
    }
    
    public TMSchema$Part getPart(JMenuItem menuItem) {
        return ((JMenu)(JMenu)menuItem).isTopLevelMenu() ? TMSchema$Part.MP_BARITEM : TMSchema$Part.MP_POPUPITEM;
    }
}
