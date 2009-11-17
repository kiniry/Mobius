package java.awt.dnd;

import java.awt.datatransfer.DataFlavor;
import java.awt.datatransfer.Transferable;
import java.awt.datatransfer.UnsupportedFlavorException;

class DragSourceContext$1 implements Transferable {
    /*synthetic*/ final DragSourceContext this$0;
    
    DragSourceContext$1(/*synthetic*/ final DragSourceContext this$0) throws UnsupportedFlavorException {
        this.this$0 = this$0;
        
    }
    
    public DataFlavor[] getTransferDataFlavors() {
        return new DataFlavor[0];
    }
    
    public boolean isDataFlavorSupported(DataFlavor flavor) {
        return false;
    }
    
    public Object getTransferData(DataFlavor flavor) throws UnsupportedFlavorException {
        throw new UnsupportedFlavorException(flavor);
    }
}
