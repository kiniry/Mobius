package java.awt;

import java.awt.event.*;
import java.lang.ref.WeakReference;
import javax.accessibility.*;

class Window$1DisposeAction implements Runnable {
    /*synthetic*/ final Window this$0;
    
    Window$1DisposeAction(/*synthetic*/ final Window this$0) {
        this.this$0 = this$0;
        
    }
    
    public void run() {
        Object[] ownedWindowArray;
        synchronized (this$0.ownedWindowList) {
            ownedWindowArray = new Object[this$0.ownedWindowList.size()];
            this$0.ownedWindowList.copyInto(ownedWindowArray);
        }
        for (int i = 0; i < ownedWindowArray.length; i++) {
            Window child = (Window)((Window)((WeakReference)((WeakReference)ownedWindowArray[i])).get());
            if (child != null) {
                child.disposeImpl();
            }
        }
        this$0.hide();
        this$0.beforeFirstShow = true;
        this$0.removeNotify();
        synchronized (Window.access$000(this$0)) {
            if (this$0.inputContext != null) {
                this$0.inputContext.dispose();
                this$0.inputContext = null;
            }
        }
        this$0.clearCurrentFocusCycleRootOnHide();
    }
}
