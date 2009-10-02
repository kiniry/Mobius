package java.awt.dnd;

import java.awt.Point;
import java.awt.datatransfer.DataFlavor;
import java.awt.datatransfer.Transferable;
import java.util.List;

public class DropTargetDragEvent extends DropTargetEvent {
    private static final long serialVersionUID = -8422265619058953682L;
    
    public DropTargetDragEvent(DropTargetContext dtc, Point cursorLocn, int dropAction, int srcActions) {
        super(dtc);
        if (cursorLocn == null) throw new NullPointerException("cursorLocn");
        if (dropAction != DnDConstants.ACTION_NONE && dropAction != DnDConstants.ACTION_COPY && dropAction != DnDConstants.ACTION_MOVE && dropAction != DnDConstants.ACTION_LINK) throw new IllegalArgumentException("dropAction" + dropAction);
        if ((srcActions & ~(DnDConstants.ACTION_COPY_OR_MOVE | DnDConstants.ACTION_LINK)) != 0) throw new IllegalArgumentException("srcActions");
        location = cursorLocn;
        actions = srcActions;
        this.dropAction = dropAction;
    }
    
    public Point getLocation() {
        return location;
    }
    
    public DataFlavor[] getCurrentDataFlavors() {
        return getDropTargetContext().getCurrentDataFlavors();
    }
    
    public List getCurrentDataFlavorsAsList() {
        return getDropTargetContext().getCurrentDataFlavorsAsList();
    }
    
    public boolean isDataFlavorSupported(DataFlavor df) {
        return getDropTargetContext().isDataFlavorSupported(df);
    }
    
    public int getSourceActions() {
        return actions;
    }
    
    public int getDropAction() {
        return dropAction;
    }
    
    public Transferable getTransferable() {
        return getDropTargetContext().getTransferable();
    }
    
    public void acceptDrag(int dragOperation) {
        getDropTargetContext().acceptDrag(dragOperation);
    }
    
    public void rejectDrag() {
        getDropTargetContext().rejectDrag();
    }
    private Point location;
    private int actions;
    private int dropAction;
}
