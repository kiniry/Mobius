package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.util.*;
import javax.swing.*;

public enum TMSchema$Control extends Enum<TMSchema$Control> {
    /*public static final*/ BUTTON /* = new TMSchema$Control("BUTTON", 0) */,
    /*public static final*/ COMBOBOX /* = new TMSchema$Control("COMBOBOX", 1) */,
    /*public static final*/ EDIT /* = new TMSchema$Control("EDIT", 2) */,
    /*public static final*/ HEADER /* = new TMSchema$Control("HEADER", 3) */,
    /*public static final*/ LISTBOX /* = new TMSchema$Control("LISTBOX", 4) */,
    /*public static final*/ LISTVIEW /* = new TMSchema$Control("LISTVIEW", 5) */,
    /*public static final*/ MENU /* = new TMSchema$Control("MENU", 6) */,
    /*public static final*/ PROGRESS /* = new TMSchema$Control("PROGRESS", 7) */,
    /*public static final*/ REBAR /* = new TMSchema$Control("REBAR", 8) */,
    /*public static final*/ SCROLLBAR /* = new TMSchema$Control("SCROLLBAR", 9) */,
    /*public static final*/ SPIN /* = new TMSchema$Control("SPIN", 10) */,
    /*public static final*/ TAB /* = new TMSchema$Control("TAB", 11) */,
    /*public static final*/ TOOLBAR /* = new TMSchema$Control("TOOLBAR", 12) */,
    /*public static final*/ TRACKBAR /* = new TMSchema$Control("TRACKBAR", 13) */,
    /*public static final*/ TREEVIEW /* = new TMSchema$Control("TREEVIEW", 14) */,
    /*public static final*/ WINDOW /* = new TMSchema$Control("WINDOW", 15) */;
    /*synthetic*/ private static final TMSchema$Control[] $VALUES = new TMSchema$Control[]{TMSchema$Control.BUTTON, TMSchema$Control.COMBOBOX, TMSchema$Control.EDIT, TMSchema$Control.HEADER, TMSchema$Control.LISTBOX, TMSchema$Control.LISTVIEW, TMSchema$Control.MENU, TMSchema$Control.PROGRESS, TMSchema$Control.REBAR, TMSchema$Control.SCROLLBAR, TMSchema$Control.SPIN, TMSchema$Control.TAB, TMSchema$Control.TOOLBAR, TMSchema$Control.TRACKBAR, TMSchema$Control.TREEVIEW, TMSchema$Control.WINDOW};
    
    public static final TMSchema$Control[] values() {
        return (TMSchema$Control[])$VALUES.clone();
    }
    
    public static TMSchema$Control valueOf(String name) {
        return (TMSchema$Control)Enum.valueOf(TMSchema.Control.class, name);
    }
    
    private TMSchema$Control(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal) {
        super($enum$name, $enum$ordinal);
    }
}
