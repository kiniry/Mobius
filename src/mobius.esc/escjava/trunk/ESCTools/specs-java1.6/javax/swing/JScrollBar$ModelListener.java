package javax.swing;

import java.io.Serializable;
import java.awt.event.AdjustmentEvent;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JScrollBar$ModelListener implements ChangeListener, Serializable {
    
    /*synthetic*/ JScrollBar$ModelListener(JScrollBar x0, javax.swing.JScrollBar$1 x1) {
        this(x0);
    }
    /*synthetic*/ final JScrollBar this$0;
    
    private JScrollBar$ModelListener(/*synthetic*/ final JScrollBar this$0) {
        this.this$0 = this$0;
        
    }
    
    public void stateChanged(ChangeEvent e) {
        Object obj = e.getSource();
        if (obj instanceof BoundedRangeModel) {
            int id = AdjustmentEvent.ADJUSTMENT_VALUE_CHANGED;
            int type = AdjustmentEvent.TRACK;
            BoundedRangeModel model = (BoundedRangeModel)(BoundedRangeModel)obj;
            int value = model.getValue();
            boolean isAdjusting = model.getValueIsAdjusting();
            JScrollBar.access$100(this$0, id, type, value, isAdjusting);
        }
    }
}
