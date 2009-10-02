package javax.swing;

import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.accessibility.*;
import java.awt.Rectangle;
import java.beans.*;

public class JScrollPane$ScrollBar extends JScrollBar implements UIResource {
    /*synthetic*/ final JScrollPane this$0;
    private boolean unitIncrementSet;
    private boolean blockIncrementSet;
    
    public JScrollPane$ScrollBar(/*synthetic*/ final JScrollPane this$0, int orientation) {
        this.this$0 = this$0;
        super(orientation);
    }
    
    public void setUnitIncrement(int unitIncrement) {
        unitIncrementSet = true;
        super.setUnitIncrement(unitIncrement);
    }
    
    public int getUnitIncrement(int direction) {
        JViewport vp = this$0.getViewport();
        if (!unitIncrementSet && (vp != null) && (vp.getView() instanceof Scrollable)) {
            Scrollable view = (Scrollable)((Scrollable)vp.getView());
            Rectangle vr = vp.getViewRect();
            return view.getScrollableUnitIncrement(vr, getOrientation(), direction);
        } else {
            return super.getUnitIncrement(direction);
        }
    }
    
    public void setBlockIncrement(int blockIncrement) {
        blockIncrementSet = true;
        super.setBlockIncrement(blockIncrement);
    }
    
    public int getBlockIncrement(int direction) {
        JViewport vp = this$0.getViewport();
        if (blockIncrementSet || vp == null) {
            return super.getBlockIncrement(direction);
        } else if (vp.getView() instanceof Scrollable) {
            Scrollable view = (Scrollable)((Scrollable)vp.getView());
            Rectangle vr = vp.getViewRect();
            return view.getScrollableBlockIncrement(vr, getOrientation(), direction);
        } else if (getOrientation() == VERTICAL) {
            return vp.getExtentSize().height;
        } else {
            return vp.getExtentSize().width;
        }
    }
}
