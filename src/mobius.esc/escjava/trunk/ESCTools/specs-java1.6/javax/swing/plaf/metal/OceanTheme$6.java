package javax.swing.plaf.metal;

import java.awt.*;
import java.util.*;
import javax.swing.*;
import javax.swing.plaf.*;

class OceanTheme$6 implements UIDefaults$LazyValue {
    /*synthetic*/ final OceanTheme this$0;
    
    OceanTheme$6(/*synthetic*/ final OceanTheme this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object createValue(UIDefaults table) {
        return new OceanTheme$COIcon(OceanTheme.access$000(this$0, "icons/ocean/collapsed.gif", table), OceanTheme.access$000(this$0, "icons/ocean/collapsed-rtl.gif", table));
    }
}
