package java.awt;

import java.awt.event.MouseEvent;
import javax.accessibility.*;

class LightweightDispatcher$3 implements Runnable {
    /*synthetic*/ final LightweightDispatcher this$0;
    /*synthetic*/ final Point val$ptSrcOrigin;
    /*synthetic*/ final MouseEvent val$mouseEvent;
    
    LightweightDispatcher$3(/*synthetic*/ final LightweightDispatcher this$0, /*synthetic*/ final MouseEvent val$mouseEvent, /*synthetic*/ final Point val$ptSrcOrigin) {
        this.this$0 = this$0;
        this.val$mouseEvent = val$mouseEvent;
        this.val$ptSrcOrigin = val$ptSrcOrigin;
        
    }
    
    public void run() {
        if (!LightweightDispatcher.access$000(this$0).isShowing()) {
            return;
        }
        Point ptDstOrigin = LightweightDispatcher.access$000(this$0).getLocationOnScreen();
        val$mouseEvent.translatePoint(val$ptSrcOrigin.x - ptDstOrigin.x, val$ptSrcOrigin.y - ptDstOrigin.y);
        Component targetOver = LightweightDispatcher.access$000(this$0).getMouseEventTarget(val$mouseEvent.getX(), val$mouseEvent.getY(), Container.INCLUDE_SELF);
        LightweightDispatcher.access$100(this$0, targetOver, val$mouseEvent);
    }
}
