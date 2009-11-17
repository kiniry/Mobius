package java.awt.datatransfer;

class Clipboard$2 implements Runnable {
    /*synthetic*/ final Clipboard this$0;
    /*synthetic*/ final FlavorListener val$listener;
    
    Clipboard$2(/*synthetic*/ final Clipboard this$0, /*synthetic*/ final FlavorListener val$listener) {
        this.this$0 = this$0;
        this.val$listener = val$listener;
        
    }
    
    public void run() {
        val$listener.flavorsChanged(new FlavorEvent(this$0));
    }
}
