package java.awt;

import javax.accessibility.*;

public class MenuBar$AccessibleAWTMenuBar extends MenuComponent$AccessibleAWTMenuComponent {
    /*synthetic*/ final MenuBar this$0;
    
    protected MenuBar$AccessibleAWTMenuBar(/*synthetic*/ final MenuBar this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    private static final long serialVersionUID = -8577604491830083815L;
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.MENU_BAR;
    }
}
