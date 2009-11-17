package java.awt.datatransfer;

import java.io.*;

public class StringSelection implements Transferable, ClipboardOwner {
    private static final int STRING = 0;
    private static final int PLAIN_TEXT = 1;
    private static final DataFlavor[] flavors = {DataFlavor.stringFlavor, DataFlavor.plainTextFlavor};
    private String data;
    
    public StringSelection(String data) {
        
        this.data = data;
    }
    
    public DataFlavor[] getTransferDataFlavors() {
        return (DataFlavor[])(DataFlavor[])flavors.clone();
    }
    
    public boolean isDataFlavorSupported(DataFlavor flavor) {
        for (int i = 0; i < flavors.length; i++) {
            if (flavor.equals(flavors[i])) {
                return true;
            }
        }
        return false;
    }
    
    public Object getTransferData(DataFlavor flavor) throws UnsupportedFlavorException, IOException {
        if (flavor.equals(flavors[STRING])) {
            return (Object)data;
        } else if (flavor.equals(flavors[PLAIN_TEXT])) {
            return new StringReader(data == null ? "" : data);
        } else {
            throw new UnsupportedFlavorException(flavor);
        }
    }
    
    public void lostOwnership(Clipboard clipboard, Transferable contents) {
    }
}
