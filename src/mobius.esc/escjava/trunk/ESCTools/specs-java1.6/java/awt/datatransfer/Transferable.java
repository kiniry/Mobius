package java.awt.datatransfer;

import java.io.IOException;

public interface Transferable {
    
    public DataFlavor[] getTransferDataFlavors();
    
    public boolean isDataFlavorSupported(DataFlavor flavor);
    
    public Object getTransferData(DataFlavor flavor) throws UnsupportedFlavorException, IOException;
}
