package java.awt;

import javax.accessibility.*;

public class Menu$AccessibleAWTMenu extends MenuItem$AccessibleAWTMenuItem {
    /*synthetic*/ final Menu this$0;
    
    protected Menu$AccessibleAWTMenu(/*synthetic*/ final Menu this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    private static final long serialVersionUID = 5228160894980069094L;
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.MENU;
    }
}
