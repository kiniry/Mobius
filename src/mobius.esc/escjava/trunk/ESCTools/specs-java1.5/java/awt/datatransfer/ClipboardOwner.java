package java.awt.datatransfer;

public interface ClipboardOwner {
    
    public void lostOwnership(Clipboard clipboard, Transferable contents);
}
