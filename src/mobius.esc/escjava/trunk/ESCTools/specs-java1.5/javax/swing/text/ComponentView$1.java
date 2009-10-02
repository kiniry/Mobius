package javax.swing.text;

import java.awt.*;
import javax.swing.event.*;

class ComponentView$1 implements Runnable {
    /*synthetic*/ final ComponentView this$0;
    
    ComponentView$1(/*synthetic*/ final ComponentView this$0) {
        this.this$0 = this$0;
        
    }
    
    public void run() {
        Document doc = this$0.getDocument();
        try {
            if (doc instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)doc).readLock();
            }
            this$0.setComponentParent();
            Container host = this$0.getContainer();
            if (host != null) {
                this$0.preferenceChanged(null, true, true);
                host.repaint();
            }
        } finally {
            if (doc instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)doc).readUnlock();
            }
        }
    }
}
