package java.awt.datatransfer;

class Clipboard$1 implements Runnable {
    /*synthetic*/ final Clipboard this$0;
    /*synthetic*/ final Transferable val$oldContents;
    /*synthetic*/ final ClipboardOwner val$oldOwner;
    
    Clipboard$1(/*synthetic*/ final Clipboard this$0, /*synthetic*/ final ClipboardOwner val$oldOwner, /*synthetic*/ final Transferable val$oldContents) {
        this.this$0 = this$0;
        this.val$oldOwner = val$oldOwner;
        this.val$oldContents = val$oldContents;
        
    }
    
    public void run() {
        val$oldOwner.lostOwnership(this$0, val$oldContents);
    }
}
