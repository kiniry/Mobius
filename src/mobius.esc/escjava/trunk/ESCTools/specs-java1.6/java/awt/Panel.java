package java.awt;

import javax.accessibility.*;

public class Panel extends Container implements Accessible {
    private static final String base = "panel";
    private static int nameCounter = 0;
    private static final long serialVersionUID = -2728009084054400034L;
    
    public Panel() {
        this(new FlowLayout());
    }
    
    public Panel(LayoutManager layout) {
        
        setLayout(layout);
    }
    
    String constructComponentName() {
        synchronized (getClass()) {
            return base + nameCounter++;
        }
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            if (peer == null) peer = getToolkit().createPanel(this);
            super.addNotify();
        }
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new Panel$AccessibleAWTPanel(this);
        }
        return accessibleContext;
    }
    {
    }
}
