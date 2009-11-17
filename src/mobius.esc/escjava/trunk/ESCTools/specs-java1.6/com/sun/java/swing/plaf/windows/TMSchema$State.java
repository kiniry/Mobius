package com.sun.java.swing.plaf.window;

import java.awt.*;
import java.util.*;
import javax.swing.*;
import sun.awt.windows.ThemeReader;

public class TMSchema$State extends Enum {
    public static final TMSChema$State ACTIVE = new TMSchema$State("ACTIVE", 0) ;
    public static final TMSChema$State ASSIST = new TMSchema$State("ASSIST", 1) ;
    public static final TMSChema$State BITMAP = new TMSchema$State("BITMAP", 2) ;
    public static final TMSChema$State CHECKED = new TMSchema$State("CHECKED", 3) ;
    public static final TMSChema$State CHECKEDDISABLED = new TMSchema$State("CHECKEDDISABLED", 4) ;
    public static final TMSChema$State CHECKEDHOT = new TMSchema$State("CHECKEDHOT", 5) ;
    public static final TMSChema$State CHECKEDNORMAL = new TMSchema$State("CHECKEDNORMAL", 6) ;
    public static final TMSChema$State CHECKEDPRESSED = new TMSchema$State("CHECKEDPRESSED", 7) ;
    public static final TMSChema$State CHECKMARKNORMAL = new TMSchema$State("CHECKMARKNORMAL", 8) ;
    public static final TMSChema$State CHECKMARKDISABLED = new TMSchema$State("CHECKMARKDISABLED", 9) ;
    public static final TMSChema$State BULLETNORMAL = new TMSchema$State("BULLETNORMAL", 10) ;
    public static final TMSChema$State BULLETDISABLED = new TMSchema$State("BULLETDISABLED", 11) ;
    public static final TMSChema$State CLOSED = new TMSchema$State("CLOSED", 12) ;
    public static final TMSChema$State DEFAULTED = new TMSchema$State("DEFAULTED", 13) ;
    public static final TMSChema$State DISABLED = new TMSchema$State("DISABLED", 14) ;
    public static final TMSChema$State DISABLEDHOT = new TMSchema$State("DISABLEDHOT", 15) ;
    public static final TMSChema$State DISABLEDPUSHED = new TMSchema$State("DISABLEDPUSHED", 16) ;
    public static final TMSChema$State DOWNDISABLED = new TMSchema$State("DOWNDISABLED", 17) ;
    public static final TMSChema$State DOWNHOT = new TMSchema$State("DOWNHOT", 18) ;
    public static final TMSChema$State DOWNNORMAL = new TMSchema$State("DOWNNORMAL", 19) ;
    public static final TMSChema$State DOWNPRESSED = new TMSchema$State("DOWNPRESSED", 20) ;
    public static final TMSChema$State FOCUSED = new TMSchema$State("FOCUSED", 21) ;
    public static final TMSChema$State HOT = new TMSchema$State("HOT", 22) ;
    public static final TMSChema$State HOTCHECKED = new TMSchema$State("HOTCHECKED", 23) ;
    public static final TMSChema$State INACTIVE = new TMSchema$State("INACTIVE", 24) ;
    public static final TMSChema$State INACTIVENORMAL = new TMSchema$State("INACTIVENORMAL", 25) ;
    public static final TMSChema$State INACTIVEHOT = new TMSchema$State("INACTIVEHOT", 26) ;
    public static final TMSChema$State INACTIVEPUSHED = new TMSchema$State("INACTIVEPUSHED", 27) ;
    public static final TMSChema$State INACTIVEDISABLED = new TMSchema$State("INACTIVEDISABLED", 28) ;
    public static final TMSChema$State LEFTDISABLED = new TMSchema$State("LEFTDISABLED", 29) ;
    public static final TMSChema$State LEFTHOT = new TMSchema$State("LEFTHOT", 30) ;
    public static final TMSChema$State LEFTNORMAL = new TMSchema$State("LEFTNORMAL", 31) ;
    public static final TMSChema$State LEFTPRESSED = new TMSchema$State("LEFTPRESSED", 32) ;
    public static final TMSChema$State MIXEDDISABLED = new TMSchema$State("MIXEDDISABLED", 33) ;
    public static final TMSChema$State MIXEDHOT = new TMSchema$State("MIXEDHOT", 34) ;
    public static final TMSChema$State MIXEDNORMAL = new TMSchema$State("MIXEDNORMAL", 35) ;
    public static final TMSChema$State MIXEDPRESSED = new TMSchema$State("MIXEDPRESSED", 36) ;
    public static final TMSChema$State NORMAL = new TMSchema$State("NORMAL", 37) ;
    public static final TMSChema$State PRESSED = new TMSchema$State("PRESSED", 38) ;
    public static final TMSChema$State OPENED = new TMSchema$State("OPENED", 39) ;
    public static final TMSChema$State PUSHED = new TMSchema$State("PUSHED", 40) ;
    public static final TMSChema$State READONLY = new TMSchema$State("READONLY", 41) ;
    public static final TMSChema$State RIGHTDISABLED = new TMSchema$State("RIGHTDISABLED", 42) ;
    public static final TMSChema$State RIGHTHOT = new TMSchema$State("RIGHTHOT", 43) ;
    public static final TMSChema$State RIGHTNORMAL = new TMSchema$State("RIGHTNORMAL", 44) ;
    public static final TMSChema$State RIGHTPRESSED = new TMSchema$State("RIGHTPRESSED", 45) ;
    public static final TMSChema$State SELECTED = new TMSchema$State("SELECTED", 46) ;
    public static final TMSChema$State UNCHECKEDDISABLED = new TMSchema$State("UNCHECKEDDISABLED", 47) ;
    public static final TMSChema$State UNCHECKEDHOT = new TMSchema$State("UNCHECKEDHOT", 48) ;
    public static final TMSChema$State UNCHECKEDNORMAL = new TMSchema$State("UNCHECKEDNORMAL", 49) ;
    public static final TMSChema$State UNCHECKEDPRESSED = new TMSchema$State("UNCHECKEDPRESSED", 50) ;
    public static final TMSChema$State UPDISABLED = new TMSchema$State("UPDISABLED", 51) ;
    public static final TMSChema$State UPHOT = new TMSchema$State("UPHOT", 52) ;
    public static final TMSChema$State UPNORMAL = new TMSchema$State("UPNORMAL", 53) ;
    public static final TMSChema$State UPPRESSED = new TMSchema$State("UPPRESSED", 54);
    /*synthetic*/ private static final TMSchema$State[] $VALUES = new TMSchema$State[]{TMSchema$State.ACTIVE, TMSchema$State.ASSIST, TMSchema$State.BITMAP, TMSchema$State.CHECKED, TMSchema$State.CHECKEDDISABLED, TMSchema$State.CHECKEDHOT, TMSchema$State.CHECKEDNORMAL, TMSchema$State.CHECKEDPRESSED, TMSchema$State.CHECKMARKNORMAL, TMSchema$State.CHECKMARKDISABLED, TMSchema$State.BULLETNORMAL, TMSchema$State.BULLETDISABLED, TMSchema$State.CLOSED, TMSchema$State.DEFAULTED, TMSchema$State.DISABLED, TMSchema$State.DISABLEDHOT, TMSchema$State.DISABLEDPUSHED, TMSchema$State.DOWNDISABLED, TMSchema$State.DOWNHOT, TMSchema$State.DOWNNORMAL, TMSchema$State.DOWNPRESSED, TMSchema$State.FOCUSED, TMSchema$State.HOT, TMSchema$State.HOTCHECKED, TMSchema$State.INACTIVE, TMSchema$State.INACTIVENORMAL, TMSchema$State.INACTIVEHOT, TMSchema$State.INACTIVEPUSHED, TMSchema$State.INACTIVEDISABLED, TMSchema$State.LEFTDISABLED, TMSchema$State.LEFTHOT, TMSchema$State.LEFTNORMAL, TMSchema$State.LEFTPRESSED, TMSchema$State.MIXEDDISABLED, TMSchema$State.MIXEDHOT, TMSchema$State.MIXEDNORMAL, TMSchema$State.MIXEDPRESSED, TMSchema$State.NORMAL, TMSchema$State.PRESSED, TMSchema$State.OPENED, TMSchema$State.PUSHED, TMSchema$State.READONLY, TMSchema$State.RIGHTDISABLED, TMSchema$State.RIGHTHOT, TMSchema$State.RIGHTNORMAL, TMSchema$State.RIGHTPRESSED, TMSchema$State.SELECTED, TMSchema$State.UNCHECKEDDISABLED, TMSchema$State.UNCHECKEDHOT, TMSchema$State.UNCHECKEDNORMAL, TMSchema$State.UNCHECKEDPRESSED, TMSchema$State.UPDISABLED, TMSchema$State.UPHOT, TMSchema$State.UPNORMAL, TMSchema$State.UPPRESSED};
    
    public static final TMSchema$State[] values() {
        return (TMSchema$State[])$VALUES.clone();
    }
    
    public static TMSchema$State valueOf(String name) {
        return (TMSchema$State)Enum.valueOf(TMSchema.State.class, name);
    }
    
    private TMSchema$State(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal) {
        super($enum$name, $enum$ordinal);
    }
    private static EnumMap stateMap;
    
    private static synchronized void initStates() {
        stateMap = new EnumMap(TMSchema.Part.class);
        stateMap.put(TMSchema$Part.EP_EDITTEXT, new TMSchema$State[]{NORMAL, HOT, SELECTED, DISABLED, FOCUSED, READONLY, ASSIST});
        stateMap.put(TMSchema$Part.BP_PUSHBUTTON, new TMSchema$State[]{NORMAL, HOT, PRESSED, DISABLED, DEFAULTED});
        stateMap.put(TMSchema$Part.BP_RADIOBUTTON, new TMSchema$State[]{UNCHECKEDNORMAL, UNCHECKEDHOT, UNCHECKEDPRESSED, UNCHECKEDDISABLED, CHECKEDNORMAL, CHECKEDHOT, CHECKEDPRESSED, CHECKEDDISABLED});
        stateMap.put(TMSchema$Part.BP_CHECKBOX, new TMSchema$State[]{UNCHECKEDNORMAL, UNCHECKEDHOT, UNCHECKEDPRESSED, UNCHECKEDDISABLED, CHECKEDNORMAL, CHECKEDHOT, CHECKEDPRESSED, CHECKEDDISABLED, MIXEDNORMAL, MIXEDHOT, MIXEDPRESSED, MIXEDDISABLED});
        TMSchema$State[] comboBoxStates = new TMSchema$State[]{NORMAL, HOT, PRESSED, DISABLED};
        stateMap.put(TMSchema$Part.CP_COMBOBOX, comboBoxStates);
        stateMap.put(TMSchema$Part.CP_DROPDOWNBUTTON, comboBoxStates);
        stateMap.put(TMSchema$Part.CP_BACKGROUND, comboBoxStates);
        stateMap.put(TMSchema$Part.CP_TRANSPARENTBACKGROUND, comboBoxStates);
        stateMap.put(TMSchema$Part.CP_BORDER, comboBoxStates);
        stateMap.put(TMSchema$Part.CP_READONLY, comboBoxStates);
        stateMap.put(TMSchema$Part.CP_DROPDOWNBUTTONRIGHT, comboBoxStates);
        stateMap.put(TMSchema$Part.CP_DROPDOWNBUTTONLEFT, comboBoxStates);
        stateMap.put(TMSchema$Part.CP_CUEBANNER, comboBoxStates);
        stateMap.put(TMSchema$Part.HP_HEADERITEM, new TMSchema$State[]{NORMAL, HOT, PRESSED});
        TMSchema$State[] scrollBarStates = new TMSchema$State[]{NORMAL, HOT, PRESSED, DISABLED};
        stateMap.put(TMSchema$Part.SBP_SCROLLBAR, scrollBarStates);
        stateMap.put(TMSchema$Part.SBP_THUMBBTNVERT, scrollBarStates);
        stateMap.put(TMSchema$Part.SBP_THUMBBTNHORZ, scrollBarStates);
        stateMap.put(TMSchema$Part.SBP_GRIPPERVERT, scrollBarStates);
        stateMap.put(TMSchema$Part.SBP_GRIPPERHORZ, scrollBarStates);
        stateMap.put(TMSchema$Part.SBP_ARROWBTN, new TMSchema$State[]{UPNORMAL, UPHOT, UPPRESSED, UPDISABLED, DOWNNORMAL, DOWNHOT, DOWNPRESSED, DOWNDISABLED, LEFTNORMAL, LEFTHOT, LEFTPRESSED, LEFTDISABLED, RIGHTNORMAL, RIGHTHOT, RIGHTPRESSED, RIGHTDISABLED});
        TMSchema$State[] spinnerStates = new TMSchema$State[]{NORMAL, HOT, PRESSED, DISABLED};
        stateMap.put(TMSchema$Part.SPNP_SPINUP, spinnerStates);
        stateMap.put(TMSchema$Part.SPNP_SPINDOWN, spinnerStates);
        stateMap.put(TMSchema$Part.TVP_GLYPH, new TMSchema$State[]{CLOSED, OPENED});
        TMSchema$State[] frameButtonStates = new TMSchema$State[]{NORMAL, HOT, PUSHED, DISABLED, INACTIVENORMAL, INACTIVEHOT, INACTIVEPUSHED, INACTIVEDISABLED};
        if (ThemeReader.getInt(TMSchema$Control.WINDOW.toString(), TMSchema$Part.WP_CLOSEBUTTON.getValue(), 1, TMSchema$Prop.IMAGECOUNT.getValue()) == 10) {
            frameButtonStates = new TMSchema$State[]{NORMAL, HOT, PUSHED, DISABLED, null, INACTIVENORMAL, INACTIVEHOT, INACTIVEPUSHED, INACTIVEDISABLED, null};
        }
        stateMap.put(TMSchema$Part.WP_MINBUTTON, frameButtonStates);
        stateMap.put(TMSchema$Part.WP_MAXBUTTON, frameButtonStates);
        stateMap.put(TMSchema$Part.WP_RESTOREBUTTON, frameButtonStates);
        stateMap.put(TMSchema$Part.WP_CLOSEBUTTON, frameButtonStates);
        stateMap.put(TMSchema$Part.TKP_TRACK, new TMSchema$State[]{NORMAL});
        stateMap.put(TMSchema$Part.TKP_TRACKVERT, new TMSchema$State[]{NORMAL});
        TMSchema$State[] sliderThumbStates = new TMSchema$State[]{NORMAL, HOT, PRESSED, FOCUSED, DISABLED};
        stateMap.put(TMSchema$Part.TKP_THUMB, sliderThumbStates);
        stateMap.put(TMSchema$Part.TKP_THUMBBOTTOM, sliderThumbStates);
        stateMap.put(TMSchema$Part.TKP_THUMBTOP, sliderThumbStates);
        stateMap.put(TMSchema$Part.TKP_THUMBVERT, sliderThumbStates);
        stateMap.put(TMSchema$Part.TKP_THUMBRIGHT, sliderThumbStates);
        TMSchema$State[] tabStates = new TMSchema$State[]{NORMAL, HOT, SELECTED, DISABLED, FOCUSED};
        stateMap.put(TMSchema$Part.TABP_TABITEM, tabStates);
        stateMap.put(TMSchema$Part.TABP_TABITEMLEFTEDGE, tabStates);
        stateMap.put(TMSchema$Part.TABP_TABITEMRIGHTEDGE, tabStates);
        stateMap.put(TMSchema$Part.TP_BUTTON, new TMSchema$State[]{NORMAL, HOT, PRESSED, DISABLED, CHECKED, HOTCHECKED});
        TMSchema$State[] frameStates = new TMSchema$State[]{ACTIVE, INACTIVE};
        stateMap.put(TMSchema$Part.WP_WINDOW, frameStates);
        stateMap.put(TMSchema$Part.WP_FRAMELEFT, frameStates);
        stateMap.put(TMSchema$Part.WP_FRAMERIGHT, frameStates);
        stateMap.put(TMSchema$Part.WP_FRAMEBOTTOM, frameStates);
        TMSchema$State[] captionStates = new TMSchema$State[]{ACTIVE, INACTIVE, DISABLED};
        stateMap.put(TMSchema$Part.WP_CAPTION, captionStates);
        stateMap.put(TMSchema$Part.WP_MINCAPTION, captionStates);
        stateMap.put(TMSchema$Part.WP_MAXCAPTION, captionStates);
        stateMap.put(TMSchema$Part.MP_BARBACKGROUND, new TMSchema$State[]{ACTIVE, INACTIVE});
        stateMap.put(TMSchema$Part.MP_BARITEM, new TMSchema$State[]{NORMAL, HOT, PUSHED, DISABLED, DISABLEDHOT, DISABLEDPUSHED});
        stateMap.put(TMSchema$Part.MP_POPUPCHECK, new TMSchema$State[]{CHECKMARKNORMAL, CHECKMARKDISABLED, BULLETNORMAL, BULLETDISABLED});
        stateMap.put(TMSchema$Part.MP_POPUPCHECKBACKGROUND, new TMSchema$State[]{DISABLEDPUSHED, NORMAL, BITMAP});
        stateMap.put(TMSchema$Part.MP_POPUPITEM, new TMSchema$State[]{NORMAL, HOT, DISABLED, DISABLEDHOT});
        stateMap.put(TMSchema$Part.MP_POPUPSUBMENU, new TMSchema$State[]{NORMAL, DISABLED});
    }
    
    public static synchronized int getValue(TMSchema$Part part, TMSchema$State state) {
        if (stateMap == null) {
            initStates();
        }
        Enum[] states = (Enum[])stateMap.get(part);
        if (states != null) {
            for (int i = 0; i < states.length; i++) {
                if (state == states[i]) {
                    return i + 1;
                }
            }
        }
        if (state == null || state == TMSchema$State.NORMAL) {
            return 1;
        }
        return 0;
    }
}
