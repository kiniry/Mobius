package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.util.*;
import javax.swing.*;

public enum TMSchema$TypeEnum extends Enum<TMSchema$TypeEnum> {
    /*public static final*/ BT_IMAGEFILE /* = new TMSchema$TypeEnum("BT_IMAGEFILE", 0, TMSchema$Prop.BGTYPE, "imagefile", 0) */,
    /*public static final*/ BT_BORDERFILL /* = new TMSchema$TypeEnum("BT_BORDERFILL", 1, TMSchema$Prop.BGTYPE, "borderfill", 1) */,
    /*public static final*/ TST_SINGLE /* = new TMSchema$TypeEnum("TST_SINGLE", 2, TMSchema$Prop.TEXTSHADOWTYPE, "single", 1) */,
    /*public static final*/ TST_CONTINUOUS /* = new TMSchema$TypeEnum("TST_CONTINUOUS", 3, TMSchema$Prop.TEXTSHADOWTYPE, "continuous", 2) */;
    /*synthetic*/ private static final TMSchema$TypeEnum[] $VALUES = new TMSchema$TypeEnum[]{TMSchema$TypeEnum.BT_IMAGEFILE, TMSchema$TypeEnum.BT_BORDERFILL, TMSchema$TypeEnum.TST_SINGLE, TMSchema$TypeEnum.TST_CONTINUOUS};
    
    public static final TMSchema$TypeEnum[] values() {
        return (TMSchema$TypeEnum[])$VALUES.clone();
    }
    
    public static TMSchema$TypeEnum valueOf(String name) {
        return (TMSchema$TypeEnum)Enum.valueOf(TMSchema.TypeEnum.class, name);
    }
    
    private TMSchema$TypeEnum(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal, TMSchema$Prop prop, String enumName, int value) {
        super($enum$name, $enum$ordinal);
        this.prop = prop;
        this.enumName = enumName;
        this.value = value;
    }
    private final TMSchema$Prop prop;
    private final String enumName;
    private final int value;
    
    public String toString() {
        return prop + "=" + enumName + "=" + value;
    }
    
    String getName() {
        return enumName;
    }
    
    static TMSchema$TypeEnum getTypeEnum(TMSchema$Prop prop, int enumval) {
        for (TMSchema$TypeEnum[] arr$ = TMSchema$TypeEnum.values(), len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            TMSchema$TypeEnum e = arr$[i$];
            {
                if (e.prop == prop && e.value == enumval) {
                    return e;
                }
            }
        }
        return null;
    }
}
