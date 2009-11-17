package javax.swing.plaf;

import java.awt.event.MouseEvent;
import javax.swing.Popup;
import javax.swing.PopupFactory;
import javax.swing.JPopupMenu;

public abstract class PopupMenuUI extends ComponentUI {
    
    public PopupMenuUI() {
        
    }
    
    public boolean isPopupTrigger(MouseEvent e) {
        return e.isPopupTrigger();
    }
    
    public Popup getPopup(JPopupMenu popup, int x, int y) {
        PopupFactory popupFactory = PopupFactory.getSharedInstance();
        return popupFactory.getPopup(popup.getInvoker(), popup, x, y);
    }
}
