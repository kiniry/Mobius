package javax.swing;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.print.*;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.table.*;
import javax.swing.border.*;
import javax.print.attribute.*;

public enum JTable$PrintMode extends Enum<JTable$PrintMode> {
    /*public static final*/ NORMAL /* = new JTable$PrintMode("NORMAL", 0) */,
    /*public static final*/ FIT_WIDTH /* = new JTable$PrintMode("FIT_WIDTH", 1) */;
    /*synthetic*/ private static final JTable$PrintMode[] $VALUES = new JTable$PrintMode[]{JTable$PrintMode.NORMAL, JTable$PrintMode.FIT_WIDTH};
    
    public static final JTable$PrintMode[] values() {
        return (JTable$PrintMode[])$VALUES.clone();
    }
    
    public static JTable$PrintMode valueOf(String name) {
        return (JTable$PrintMode)Enum.valueOf(JTable.PrintMode.class, name);
    }
    
    private JTable$PrintMode(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal) {
        super($enum$name, $enum$ordinal);
    }
}
