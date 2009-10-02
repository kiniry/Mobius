package javax.swing;

import java.awt.*;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.List;
import java.util.Map;

class PopupFactory$HeavyWeightPopup$1 extends WindowAdapter {
    /*synthetic*/ final Window val$w;
    
    PopupFactory$HeavyWeightPopup$1(/*synthetic*/ final Window val$w) {
        this.val$w = val$w;
        
    }
    
    public void windowClosed(WindowEvent e) {
        List popups;
        synchronized (PopupFactory.HeavyWeightPopup.class) {
            Map heavyPopupCache2 = PopupFactory.HeavyWeightPopup.access$000();
            popups = (List)(List)heavyPopupCache2.remove(val$w);
        }
        if (popups != null) {
            for (int counter = popups.size() - 1; counter >= 0; counter--) {
                ((PopupFactory$HeavyWeightPopup)(PopupFactory$HeavyWeightPopup)popups.get(counter))._dispose();
            }
        }
    }
}
