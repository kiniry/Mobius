package javax.swing.plaf.metal;

import java.awt.*;
import java.util.*;
import javax.swing.*;
import javax.swing.plaf.*;

class OceanTheme$4 implements UIDefaults$LazyValue {
    /*synthetic*/ final OceanTheme this$0;
    
    OceanTheme$4(/*synthetic*/ final OceanTheme this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object createValue(UIDefaults table) {
        return new OceanTheme$IFIcon(OceanTheme.access$000(this$0, "icons/ocean/maximize.gif", table), OceanTheme.access$000(this$0, "icons/ocean/maximize-pressed.gif", table));
    }
}
