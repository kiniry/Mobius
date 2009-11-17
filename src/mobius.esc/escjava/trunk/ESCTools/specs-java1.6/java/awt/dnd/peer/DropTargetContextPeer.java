package java.awt.dnd.peer;

import java.awt.datatransfer.DataFlavor;
import java.awt.datatransfer.Transferable;
import java.awt.dnd.DropTarget;
import java.awt.dnd.InvalidDnDOperationException;

public interface DropTargetContextPeer {
    
    void setTargetActions(int actions);
    
    int getTargetActions();
    
    DropTarget getDropTarget();
    
    DataFlavor[] getTransferDataFlavors();
    
    Transferable getTransferable() throws InvalidDnDOperationException;
    
    boolean isTransferableJVMLocal();
    
    void acceptDrag(int dragAction);
    
    void rejectDrag();
    
    void acceptDrop(int dropAction);
    
    void rejectDrop();
    
    void dropComplete(boolean success);
}
