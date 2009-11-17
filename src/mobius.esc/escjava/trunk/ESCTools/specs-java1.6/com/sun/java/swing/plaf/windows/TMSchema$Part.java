package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.util.*;
import javax.swing.*;

public class TMSchema$Part extends Enum {
    public static final TMSchema$Part  MENU  = new TMSchema$Part("MENU", 0, TMSchema$Control.MENU, 0);
    public static final TMSchema$Part  MP_BARBACKGROUND  = new TMSchema$Part("MP_BARBACKGROUND", 1, TMSchema$Control.MENU, 7);
    public static final TMSchema$Part  MP_BARITEM  = new TMSchema$Part("MP_BARITEM", 2, TMSchema$Control.MENU, 8);
    public static final TMSchema$Part  MP_POPUPBACKGROUND = new TMSchema$Part("MP_POPUPBACKGROUND", 3, TMSchema$Control.MENU, 9);
    public static final  TMSchema$Part MP_POPUPBORDERS = new TMSchema$Part("MP_POPUPBORDERS", 4, TMSchema$Control.MENU, 10);
    public static final  TMSchema$Part MP_POPUPCHECK = new TMSchema$Part("MP_POPUPCHECK", 5, TMSchema$Control.MENU, 11) ;
    public static final  TMSchema$Part MP_POPUPCHECKBACKGROUND = new TMSchema$Part("MP_POPUPCHECKBACKGROUND", 6, TMSchema$Control.MENU, 12) ;
    public static final  TMSchema$Part MP_POPUPGUTTER = new TMSchema$Part("MP_POPUPGUTTER", 7, TMSchema$Control.MENU, 13) ;
    public static final  TMSchema$Part MP_POPUPITEM = new TMSchema$Part("MP_POPUPITEM", 8, TMSchema$Control.MENU, 14) ;
    public static final  TMSchema$Part MP_POPUPSEPARATOR = new TMSchema$Part("MP_POPUPSEPARATOR", 9, TMSchema$Control.MENU, 15);
    public static final  TMSchema$Part MP_POPUPSUBMENU = new TMSchema$Part("MP_POPUPSUBMENU", 10, TMSchema$Control.MENU, 16);
    public static final  TMSchema$Part BP_PUSHBUTTON = new TMSchema$Part("BP_PUSHBUTTON", 11, TMSchema$Control.BUTTON, 1);
    public static final  TMSchema$Part BP_RADIOBUTTON = new TMSchema$Part("BP_RADIOBUTTON", 12, TMSchema$Control.BUTTON, 2);
    public static final  TMSchema$Part BP_CHECKBOX = new TMSchema$Part("BP_CHECKBOX", 13, TMSchema$Control.BUTTON, 3);
    public static final  TMSchema$Part BP_GROUPBOX = new TMSchema$Part("BP_GROUPBOX", 14, TMSchema$Control.BUTTON, 4) ;
    public static final  TMSchema$Part CP_COMBOBOX = new TMSchema$Part("CP_COMBOBOX", 15, TMSchema$Control.COMBOBOX, 0) ;
    public static final  TMSchema$Part CP_DROPDOWNBUTTON = new TMSchema$Part("CP_DROPDOWNBUTTON", 16, TMSchema$Control.COMBOBOX, 1);
    public static final  TMSchema$Part CP_BACKGROUND = new TMSchema$Part("CP_BACKGROUND", 17, TMSchema$Control.COMBOBOX, 2);
    public static final  TMSchema$Part CP_TRANSPARENTBACKGROUND = new TMSchema$Part("CP_TRANSPARENTBACKGROUND", 18, TMSchema$Control.COMBOBOX, 3);
    public static final  TMSchema$Part CP_BORDER = new TMSchema$Part("CP_BORDER", 19, TMSchema$Control.COMBOBOX, 4) ;
    public static final  TMSchema$Part CP_READONLY = new TMSchema$Part("CP_READONLY", 20, TMSchema$Control.COMBOBOX, 5);
    public static final  TMSchema$Part CP_DROPDOWNBUTTONRIGHT = new TMSchema$Part("CP_DROPDOWNBUTTONRIGHT", 21, TMSchema$Control.COMBOBOX, 6);
    public static final  TMSchema$Part CP_DROPDOWNBUTTONLEFT  = new TMSchema$Part("CP_DROPDOWNBUTTONLEFT", 22, TMSchema$Control.COMBOBOX, 7);
    public static final  TMSchema$Part CP_CUEBANNER = new TMSchema$Part("CP_CUEBANNER", 23, TMSchema$Control.COMBOBOX, 8);
    public static final  TMSchema$Part EP_EDIT = new TMSchema$Part("EP_EDIT", 24, TMSchema$Control.EDIT, 0);
    public static final  TMSchema$Part EP_EDITTEXT = new TMSchema$Part("EP_EDITTEXT", 25, TMSchema$Control.EDIT, 1) ;
    public static final  TMSchema$Part HP_HEADERITEM = new TMSchema$Part("HP_HEADERITEM", 26, TMSchema$Control.HEADER, 1) ;
    public static final  TMSchema$Part HP_HEADERSORTARROW = new TMSchema$Part("HP_HEADERSORTARROW", 27, TMSchema$Control.HEADER, 4);
    public static final  TMSchema$Part LBP_LISTBOX = new TMSchema$Part("LBP_LISTBOX", 28, TMSchema$Control.LISTBOX, 0);
    public static final  TMSchema$Part LVP_LISTVIEW = new TMSchema$Part("LVP_LISTVIEW", 29, TMSchema$Control.LISTVIEW, 0);
    public static final  TMSchema$Part PP_PROGRESS = new TMSchema$Part("PP_PROGRESS", 30, TMSchema$Control.PROGRESS, 0);
    public static final  TMSchema$Part PP_BAR = new TMSchema$Part("PP_BAR", 31, TMSchema$Control.PROGRESS, 1);
    public static final  TMSchema$Part PP_BARVERT = new TMSchema$Part("PP_BARVERT", 32, TMSchema$Control.PROGRESS, 2);
    public static final  TMSchema$Part PP_CHUNK = new TMSchema$Part("PP_CHUNK", 33, TMSchema$Control.PROGRESS, 3);
    public static final  TMSchema$Part PP_CHUNKVERT = new TMSchema$Part("PP_CHUNKVERT", 34, TMSchema$Control.PROGRESS, 4);
    public static final  TMSchema$Part RP_GRIPPER  = new TMSchema$Part("RP_GRIPPER", 35, TMSchema$Control.REBAR, 1);
    public static final  TMSchema$Part RP_GRIPPERVERT  = new TMSchema$Part("RP_GRIPPERVERT", 36, TMSchema$Control.REBAR, 2);
    public static final  TMSchema$Part SBP_SCROLLBAR  = new TMSchema$Part("SBP_SCROLLBAR", 37, TMSchema$Control.SCROLLBAR, 0);
    public static final  TMSchema$Part SBP_ARROWBTN  = new TMSchema$Part("SBP_ARROWBTN", 38, TMSchema$Control.SCROLLBAR, 1);
    public static final  TMSchema$Part SBP_THUMBBTNHORZ = new TMSchema$Part("SBP_THUMBBTNHORZ", 39, TMSchema$Control.SCROLLBAR, 2);
    public static final  TMSchema$Part SBP_THUMBBTNVERT = new TMSchema$Part("SBP_THUMBBTNVERT", 40, TMSchema$Control.SCROLLBAR, 3);
    public static final  TMSchema$Part SBP_LOWERTRACKHORZ  = new TMSchema$Part("SBP_LOWERTRACKHORZ", 41, TMSchema$Control.SCROLLBAR, 4);
    public static final  TMSchema$Part SBP_UPPERTRACKHORZ  = new TMSchema$Part("SBP_UPPERTRACKHORZ", 42, TMSchema$Control.SCROLLBAR, 5);
    public static final  TMSchema$Part SBP_LOWERTRACKVERT  = new TMSchema$Part("SBP_LOWERTRACKVERT", 43, TMSchema$Control.SCROLLBAR, 6);
    public static final  TMSchema$Part SBP_UPPERTRACKVERT  = new TMSchema$Part("SBP_UPPERTRACKVERT", 44, TMSchema$Control.SCROLLBAR, 7);
    public static final  TMSchema$Part SBP_GRIPPERHORZ  = new TMSchema$Part("SBP_GRIPPERHORZ", 45, TMSchema$Control.SCROLLBAR, 8);
    public static final  TMSchema$Part SBP_GRIPPERVERT  = new TMSchema$Part("SBP_GRIPPERVERT", 46, TMSchema$Control.SCROLLBAR, 9);
    public static final  TMSchema$Part SBP_SIZEBOX  = new TMSchema$Part("SBP_SIZEBOX", 47, TMSchema$Control.SCROLLBAR, 10);
    public static final  TMSchema$Part SPNP_SPINUP  = new TMSchema$Part("SPNP_SPINUP", 48, TMSchema$Control.SPIN, 1);
    public static final  TMSchema$Part SPNP_SPINDOWN  = new TMSchema$Part("SPNP_SPINDOWN", 49, TMSchema$Control.SPIN, 2);
    public static final  TMSchema$Part TABP_TABITEM  = new TMSchema$Part("TABP_TABITEM", 50, TMSchema$Control.TAB, 1);
    public static final  TMSchema$Part TABP_TABITEMLEFTEDGE  = new TMSchema$Part("TABP_TABITEMLEFTEDGE", 51, TMSchema$Control.TAB, 2);
    public static final  TMSchema$Part TABP_TABITEMRIGHTEDGE  = new TMSchema$Part("TABP_TABITEMRIGHTEDGE", 52, TMSchema$Control.TAB, 3);
    public static final  TMSchema$Part TABP_PANE  = new TMSchema$Part("TABP_PANE", 53, TMSchema$Control.TAB, 9);
    public static final  TMSchema$Part TP_TOOLBAR  = new TMSchema$Part("TP_TOOLBAR", 54, TMSchema$Control.TOOLBAR, 0);
    public static final  TMSchema$Part TP_BUTTON  = new TMSchema$Part("TP_BUTTON", 55, TMSchema$Control.TOOLBAR, 1);
    public static final  TMSchema$Part TP_SEPARATOR  = new TMSchema$Part("TP_SEPARATOR", 56, TMSchema$Control.TOOLBAR, 5);
    public static final  TMSchema$Part TP_SEPARATORVERT = new TMSchema$Part("TP_SEPARATORVERT", 57, TMSchema$Control.TOOLBAR, 6) ;
    public static final  TMSchema$Part TKP_TRACK = new TMSchema$Part("TKP_TRACK", 58, TMSchema$Control.TRACKBAR, 1);
    public static final  TMSchema$Part TKP_TRACKVERT = new TMSchema$Part("TKP_TRACKVERT", 59, TMSchema$Control.TRACKBAR, 2);
    public static final  TMSchema$Part TKP_THUMB = new TMSchema$Part("TKP_THUMB", 60, TMSchema$Control.TRACKBAR, 3);
    public static final  TMSchema$Part TKP_THUMBBOTTOM = new TMSchema$Part("TKP_THUMBBOTTOM", 61, TMSchema$Control.TRACKBAR, 4);
    public static final  TMSchema$Part TKP_THUMBTOP = new TMSchema$Part("TKP_THUMBTOP", 62, TMSchema$Control.TRACKBAR, 5);
    public static final  TMSchema$Part TKP_THUMBVERT = new TMSchema$Part("TKP_THUMBVERT", 63, TMSchema$Control.TRACKBAR, 6);
    public static final  TMSchema$Part TKP_THUMBLEFT = new TMSchema$Part("TKP_THUMBLEFT", 64, TMSchema$Control.TRACKBAR, 7);
    public static final  TMSchema$Part TKP_THUMBRIGHT = new TMSchema$Part("TKP_THUMBRIGHT", 65, TMSchema$Control.TRACKBAR, 8);
    public static final  TMSchema$Part TKP_TICS  = new TMSchema$Part("TKP_TICS", 66, TMSchema$Control.TRACKBAR, 9) ;
    public static final  TMSchema$Part TKP_TICSVERT = new TMSchema$Part("TKP_TICSVERT", 67, TMSchema$Control.TRACKBAR, 10);
    public static final  TMSchema$Part TVP_TREEVIEW  = new TMSchema$Part("TVP_TREEVIEW", 68, TMSchema$Control.TREEVIEW, 0);
    public static final  TMSchema$Part TVP_GLYPH = new TMSchema$Part("TVP_GLYPH", 69, TMSchema$Control.TREEVIEW, 2);
    public static final  TMSchema$Part WP_WINDOW = new TMSchema$Part("WP_WINDOW", 70, TMSchema$Control.WINDOW, 0);
    public static final  TMSchema$Part WP_CAPTION = new TMSchema$Part("WP_CAPTION", 71, TMSchema$Control.WINDOW, 1);
    public static final  TMSchema$Part WP_MINCAPTION = new TMSchema$Part("WP_MINCAPTION", 72, TMSchema$Control.WINDOW, 3);
    public static final  TMSchema$Part WP_MAXCAPTION = new TMSchema$Part("WP_MAXCAPTION", 73, TMSchema$Control.WINDOW, 5);
    public static final  TMSchema$Part WP_FRAMELEFT = new TMSchema$Part("WP_FRAMELEFT", 74, TMSchema$Control.WINDOW, 7);
    public static final  TMSchema$Part WP_FRAMERIGHT = new TMSchema$Part("WP_FRAMERIGHT", 75, TMSchema$Control.WINDOW, 8);
    public static final  TMSchema$Part WP_FRAMEBOTTOM = new TMSchema$Part("WP_FRAMEBOTTOM", 76, TMSchema$Control.WINDOW, 9);
    public static final  TMSchema$Part WP_SYSBUTTON  = new TMSchema$Part("WP_SYSBUTTON", 77, TMSchema$Control.WINDOW, 13);
    public static final  TMSchema$Part WP_MDISYSBUTTON = new TMSchema$Part("WP_MDISYSBUTTON", 78, TMSchema$Control.WINDOW, 14);
    public static final  TMSchema$Part WP_MINBUTTON = new TMSchema$Part("WP_MINBUTTON", 79, TMSchema$Control.WINDOW, 15);
    public static final  TMSchema$Part WP_MDIMINBUTTON = new TMSchema$Part("WP_MDIMINBUTTON", 80, TMSchema$Control.WINDOW, 16);
    public static final  TMSchema$Part WP_MAXBUTTON = new TMSchema$Part("WP_MAXBUTTON", 81, TMSchema$Control.WINDOW, 17);
    public static final  TMSchema$Part WP_CLOSEBUTTON = new TMSchema$Part("WP_CLOSEBUTTON", 82, TMSchema$Control.WINDOW, 18);
    public static final  TMSchema$Part WP_MDICLOSEBUTTON = new TMSchema$Part("WP_MDICLOSEBUTTON", 83, TMSchema$Control.WINDOW, 20);
    public static final  TMSchema$Part WP_RESTOREBUTTON = new TMSchema$Part("WP_RESTOREBUTTON", 84, TMSchema$Control.WINDOW, 21);
    public static final  TMSchema$Part WP_MDIRESTOREBUTTON = new TMSchema$Part("WP_MDIRESTOREBUTTON", 85, TMSchema$Control.WINDOW, 22);
    /*synthetic*/ private static final TMSchema$Part[] $VALUES = new TMSchema$Part[]{TMSchema$Part.MENU, TMSchema$Part.MP_BARBACKGROUND, TMSchema$Part.MP_BARITEM, TMSchema$Part.MP_POPUPBACKGROUND, TMSchema$Part.MP_POPUPBORDERS, TMSchema$Part.MP_POPUPCHECK, TMSchema$Part.MP_POPUPCHECKBACKGROUND, TMSchema$Part.MP_POPUPGUTTER, TMSchema$Part.MP_POPUPITEM, TMSchema$Part.MP_POPUPSEPARATOR, TMSchema$Part.MP_POPUPSUBMENU, TMSchema$Part.BP_PUSHBUTTON, TMSchema$Part.BP_RADIOBUTTON, TMSchema$Part.BP_CHECKBOX, TMSchema$Part.BP_GROUPBOX, TMSchema$Part.CP_COMBOBOX, TMSchema$Part.CP_DROPDOWNBUTTON, TMSchema$Part.CP_BACKGROUND, TMSchema$Part.CP_TRANSPARENTBACKGROUND, TMSchema$Part.CP_BORDER, TMSchema$Part.CP_READONLY, TMSchema$Part.CP_DROPDOWNBUTTONRIGHT, TMSchema$Part.CP_DROPDOWNBUTTONLEFT, TMSchema$Part.CP_CUEBANNER, TMSchema$Part.EP_EDIT, TMSchema$Part.EP_EDITTEXT, TMSchema$Part.HP_HEADERITEM, TMSchema$Part.HP_HEADERSORTARROW, TMSchema$Part.LBP_LISTBOX, TMSchema$Part.LVP_LISTVIEW, TMSchema$Part.PP_PROGRESS, TMSchema$Part.PP_BAR, TMSchema$Part.PP_BARVERT, TMSchema$Part.PP_CHUNK, TMSchema$Part.PP_CHUNKVERT, TMSchema$Part.RP_GRIPPER, TMSchema$Part.RP_GRIPPERVERT, TMSchema$Part.SBP_SCROLLBAR, TMSchema$Part.SBP_ARROWBTN, TMSchema$Part.SBP_THUMBBTNHORZ, TMSchema$Part.SBP_THUMBBTNVERT, TMSchema$Part.SBP_LOWERTRACKHORZ, TMSchema$Part.SBP_UPPERTRACKHORZ, TMSchema$Part.SBP_LOWERTRACKVERT, TMSchema$Part.SBP_UPPERTRACKVERT, TMSchema$Part.SBP_GRIPPERHORZ, TMSchema$Part.SBP_GRIPPERVERT, TMSchema$Part.SBP_SIZEBOX, TMSchema$Part.SPNP_SPINUP, TMSchema$Part.SPNP_SPINDOWN, TMSchema$Part.TABP_TABITEM, TMSchema$Part.TABP_TABITEMLEFTEDGE, TMSchema$Part.TABP_TABITEMRIGHTEDGE, TMSchema$Part.TABP_PANE, TMSchema$Part.TP_TOOLBAR, TMSchema$Part.TP_BUTTON, TMSchema$Part.TP_SEPARATOR, TMSchema$Part.TP_SEPARATORVERT, TMSchema$Part.TKP_TRACK, TMSchema$Part.TKP_TRACKVERT, TMSchema$Part.TKP_THUMB, TMSchema$Part.TKP_THUMBBOTTOM, TMSchema$Part.TKP_THUMBTOP, TMSchema$Part.TKP_THUMBVERT, TMSchema$Part.TKP_THUMBLEFT, TMSchema$Part.TKP_THUMBRIGHT, TMSchema$Part.TKP_TICS, TMSchema$Part.TKP_TICSVERT, TMSchema$Part.TVP_TREEVIEW, TMSchema$Part.TVP_GLYPH, TMSchema$Part.WP_WINDOW, TMSchema$Part.WP_CAPTION, TMSchema$Part.WP_MINCAPTION, TMSchema$Part.WP_MAXCAPTION, TMSchema$Part.WP_FRAMELEFT, TMSchema$Part.WP_FRAMERIGHT, TMSchema$Part.WP_FRAMEBOTTOM, TMSchema$Part.WP_SYSBUTTON, TMSchema$Part.WP_MDISYSBUTTON, TMSchema$Part.WP_MINBUTTON, TMSchema$Part.WP_MDIMINBUTTON, TMSchema$Part.WP_MAXBUTTON, TMSchema$Part.WP_CLOSEBUTTON, TMSchema$Part.WP_MDICLOSEBUTTON, TMSchema$Part.WP_RESTOREBUTTON, TMSchema$Part.WP_MDIRESTOREBUTTON};
    
    public static final TMSchema$Part[] values() {
        return (TMSchema$Part[])$VALUES.clone();
    }
    
    public static TMSchema$Part valueOf(String name) {
        return (TMSchema$Part)Enum.valueOf(TMSchema.Part.class, name);
    }
    private final TMSchema$Control control;
    private final int value;
    
    private TMSchema$Part(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal, TMSchema$Control control, int value) {
        super($enum$name, $enum$ordinal);
        this.control = control;
        this.value = value;
    }
    
    public int getValue() {
        return value;
    }
    
    public String getControlName(Component component) {
        String str = "";
        if (component instanceof JComponent) {
            JComponent c = (JComponent)(JComponent)component;
            String subAppName = (String)(String)c.getClientProperty("XPStyle.subAppName");
            if (subAppName != null) {
                str = subAppName + "::";
            }
        }
        return str + control.toString();
    }
    
    public String toString() {
        return control.toString() + "." + name();
    }
}
