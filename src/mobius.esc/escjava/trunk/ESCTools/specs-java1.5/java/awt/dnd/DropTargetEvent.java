package java.awt.dnd;

import java.awt.dnd.DropTargetContext;

public class DropTargetEvent extends java.util.EventObject {
    private static final long serialVersionUID = 2821229066521922993L;
    
    public DropTargetEvent(DropTargetContext dtc) {
        super(dtc.getDropTarget());
        context = dtc;
    }
    
    public DropTargetContext getDropTargetContext() {
        return context;
    }
    protected DropTargetContext context;
}
