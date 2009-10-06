package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.util.*;
import javax.swing.*;

public class TMSchema$Control extends Enum {
    public static final TMSchema$Control BUTTON = new TMSchema$Control("BUTTON", 0) ;
    public static final TMSchema$Control COMBOBOX = new TMSchema$Control("COMBOBOX", 1) ;
    public static final TMSchema$Control EDIT = new TMSchema$Control("EDIT", 2) ;
    public static final TMSchema$Control HEADER = new TMSchema$Control("HEADER", 3) ;
    public static final TMSchema$Control LISTBOX = new TMSchema$Control("LISTBOX", 4) ;
    public static final TMSchema$Control LISTVIEW = new TMSchema$Control("LISTVIEW", 5) ;
    public static final TMSchema$Control MENU = new TMSchema$Control("MENU", 6) ;
    public static final TMSchema$Control PROGRESS = new TMSchema$Control("PROGRESS", 7) ;
    public static final TMSchema$Control REBAR = new TMSchema$Control("REBAR", 8) ;
    public static final TMSchema$Control SCROLLBAR = new TMSchema$Control("SCROLLBAR", 9) ;
    public static final TMSchema$Control SPIN = new TMSchema$Control("SPIN", 10) ;
    public static final TMSchema$Control TAB = new TMSchema$Control("TAB", 11) ;
    public static final TMSchema$Control TOOLBAR = new TMSchema$Control("TOOLBAR", 12) ;
    public static final TMSchema$Control TRACKBAR = new TMSchema$Control("TRACKBAR", 13) ;
    public static final TMSchema$Control TREEVIEW = new TMSchema$Control("TREEVIEW", 14) ;
    public static final TMSchema$Control WINDOW = new TMSchema$Control("WINDOW", 15);
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
