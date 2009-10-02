package java.awt.dnd;

import java.awt.datatransfer.DataFlavor;
import java.awt.datatransfer.Transferable;
import java.awt.datatransfer.UnsupportedFlavorException;
import java.io.IOException;

public class DropTargetContext$TransferableProxy implements Transferable {
    /*synthetic*/ final DropTargetContext this$0;
    
    DropTargetContext$TransferableProxy(/*synthetic*/ final DropTargetContext this$0, Transferable t, boolean local) {
        this.this$0 = this$0;
        
        proxy = new sun.awt.datatransfer.TransferableProxy(t, local);
        transferable = t;
        isLocal = local;
    }
    
    public DataFlavor[] getTransferDataFlavors() {
        return proxy.getTransferDataFlavors();
    }
    
    public boolean isDataFlavorSupported(DataFlavor flavor) {
        return proxy.isDataFlavorSupported(flavor);
    }
    
    public Object getTransferData(DataFlavor df) throws UnsupportedFlavorException, IOException {
        return proxy.getTransferData(df);
    }
    protected Transferable transferable;
    protected boolean isLocal;
    private sun.awt.datatransfer.TransferableProxy proxy;
}
