package javax.swing.plaf.metal;

import java.awt.*;
import java.util.*;
import javax.swing.*;
import javax.swing.plaf.*;

class OceanTheme$1 implements UIDefaults$LazyValue {
    /*synthetic*/ final OceanTheme this$0;
    
    OceanTheme$1(/*synthetic*/ final OceanTheme this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object createValue(UIDefaults table) {
        return new OceanTheme$IFIcon(OceanTheme.access$000(this$0, "icons/ocean/close.gif", table), OceanTheme.access$000(this$0, "icons/ocean/close-pressed.gif", table));
    }
}
