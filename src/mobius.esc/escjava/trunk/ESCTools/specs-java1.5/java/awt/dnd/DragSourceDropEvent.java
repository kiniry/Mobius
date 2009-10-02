package java.awt.dnd;

public class DragSourceDropEvent extends DragSourceEvent {
    private static final long serialVersionUID = -5571321229470821891L;
    
    public DragSourceDropEvent(DragSourceContext dsc, int action, boolean success) {
        super(dsc);
        dropSuccess = success;
        dropAction = action;
    }
    
    public DragSourceDropEvent(DragSourceContext dsc, int action, boolean success, int x, int y) {
        super(dsc, x, y);
        dropSuccess = success;
        dropAction = action;
    }
    
    public DragSourceDropEvent(DragSourceContext dsc) {
        super(dsc);
        dropSuccess = false;
    }
    
    public boolean getDropSuccess() {
        return dropSuccess;
    }
    
    public int getDropAction() {
        return dropAction;
    }
    private boolean dropSuccess;
    private int dropAction = DnDConstants.ACTION_NONE;
}
