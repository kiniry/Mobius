package javax.swing.plaf.basic;

import java.awt.event.*;
import java.io.*;
import java.util.*;
import java.lang.reflect.*;
import javax.sound.sampled.*;
import javax.swing.UIDefaults;
import javax.swing.border.*;
import javax.swing.plaf.*;

class BasicLookAndFeel$1 implements UIDefaults$ActiveValue {
    /*synthetic*/ final BasicLookAndFeel this$0;
    
    BasicLookAndFeel$1(/*synthetic*/ final BasicLookAndFeel this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object createValue(UIDefaults table) {
        return new DefaultListCellRenderer$UIResource();
    }
}
