package java.awt;

import javax.accessibility.*;

public class Label$AccessibleAWTLabel extends Component$AccessibleAWTComponent {
    /*synthetic*/ final Label this$0;
    private static final long serialVersionUID = -3568967560160480438L;
    
    public Label$AccessibleAWTLabel(/*synthetic*/ final Label this$0) {
        super(this$0);
        this.this$0 = this$0;

    }
    
    public String getAccessibleName() {
        if (accessibleName != null) {
            return accessibleName;
        } else {
            if (this$0.getText() == null) {
                return super.getAccessibleName();
            } else {
                return this$0.getText();
            }
        }
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.LABEL;
    }
}
