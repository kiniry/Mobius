package java.awt.event;

import java.util.EventListener;

public interface AdjustmentListener extends EventListener {
    
    public void adjustmentValueChanged(AdjustmentEvent e);
}
