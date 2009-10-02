package javax.swing.plaf.basic;

import java.awt.event.*;
import java.io.*;
import java.util.*;
import java.lang.reflect.*;
import javax.sound.sampled.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeEvent;

class BasicLookAndFeel$3 implements PropertyChangeListener {
    /*synthetic*/ final BasicLookAndFeel this$0;
    
    BasicLookAndFeel$3(/*synthetic*/ final BasicLookAndFeel this$0) {
        this.this$0 = this$0;
        
    }
    
    public void propertyChange(PropertyChangeEvent prpChg) {
        this$0.uninitialize();
    }
}
