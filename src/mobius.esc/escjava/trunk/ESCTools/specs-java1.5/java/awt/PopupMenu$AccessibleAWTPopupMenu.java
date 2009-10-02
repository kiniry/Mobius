package java.awt;

import javax.accessibility.*;

public class PopupMenu$AccessibleAWTPopupMenu extends Menu$AccessibleAWTMenu {
    /*synthetic*/ final PopupMenu this$0;
    
    protected PopupMenu$AccessibleAWTPopupMenu(/*synthetic*/ final PopupMenu this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    private static final long serialVersionUID = -4282044795947239955L;
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.POPUP_MENU;
    }
}
