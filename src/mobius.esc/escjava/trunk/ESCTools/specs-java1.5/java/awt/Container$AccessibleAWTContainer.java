package java.awt;

import java.awt.event.ContainerListener;
import javax.accessibility.*;
import java.beans.PropertyChangeListener;

public class Container$AccessibleAWTContainer extends Component$AccessibleAWTComponent {
    /*synthetic*/ final Container this$0;
    
    protected Container$AccessibleAWTContainer(/*synthetic*/ final Container this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    private static final long serialVersionUID = 5081320404842566097L;
    
    public int getAccessibleChildrenCount() {
        return this$0.getAccessibleChildrenCount();
    }
    
    public Accessible getAccessibleChild(int i) {
        return this$0.getAccessibleChild(i);
    }
    
    public Accessible getAccessibleAt(Point p) {
        return this$0.getAccessibleAt(p);
    }
    protected ContainerListener accessibleContainerHandler = null;
    {
    }
    
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        if (accessibleContainerHandler == null) {
            accessibleContainerHandler = new Container$AccessibleAWTContainer$AccessibleContainerHandler(this);
            this$0.addContainerListener(accessibleContainerHandler);
        }
        super.addPropertyChangeListener(listener);
    }
}
