package com.sun.java.swing.plaf.windows;

import javax.swing.*;
import java.awt.*;
import java.io.Serializable;
import com.sun.java.swing.plaf.windows.TMSchema.*;

public class WindowsIconFactory implements Serializable {
    {
    }
    
    public WindowsIconFactory() {
        
    }
    private static Icon frame_closeIcon;
    private static Icon frame_iconifyIcon;
    private static Icon frame_maxIcon;
    private static Icon frame_minIcon;
    private static Icon frame_resizeIcon;
    private static Icon checkBoxIcon;
    private static Icon radioButtonIcon;
    private static Icon checkBoxMenuItemIcon;
    private static Icon radioButtonMenuItemIcon;
    private static Icon menuItemCheckIcon;
    private static Icon menuItemArrowIcon;
    private static Icon menuArrowIcon;
    private static WindowsIconFactory$VistaMenuItemCheckIconFactory menuItemCheckIconFactory;
    
    public static Icon getMenuItemCheckIcon() {
        if (menuItemCheckIcon == null) {
            menuItemCheckIcon = new WindowsIconFactory$MenuItemCheckIcon(null);
        }
        return menuItemCheckIcon;
    }
    
    public static Icon getMenuItemArrowIcon() {
        if (menuItemArrowIcon == null) {
            menuItemArrowIcon = new WindowsIconFactory$MenuItemArrowIcon(null);
        }
        return menuItemArrowIcon;
    }
    
    public static Icon getMenuArrowIcon() {
        if (menuArrowIcon == null) {
            menuArrowIcon = new WindowsIconFactory$MenuArrowIcon(null);
        }
        return menuArrowIcon;
    }
    
    public static Icon getCheckBoxIcon() {
        if (checkBoxIcon == null) {
            checkBoxIcon = new WindowsIconFactory$CheckBoxIcon(null);
        }
        return checkBoxIcon;
    }
    
    public static Icon getRadioButtonIcon() {
        if (radioButtonIcon == null) {
            radioButtonIcon = new WindowsIconFactory$RadioButtonIcon(null);
        }
        return radioButtonIcon;
    }
    
    public static Icon getCheckBoxMenuItemIcon() {
        if (checkBoxMenuItemIcon == null) {
            checkBoxMenuItemIcon = new WindowsIconFactory$CheckBoxMenuItemIcon(null);
        }
        return checkBoxMenuItemIcon;
    }
    
    public static Icon getRadioButtonMenuItemIcon() {
        if (radioButtonMenuItemIcon == null) {
            radioButtonMenuItemIcon = new WindowsIconFactory$RadioButtonMenuItemIcon(null);
        }
        return radioButtonMenuItemIcon;
    }
    
    static synchronized WindowsIconFactory$VistaMenuItemCheckIconFactory getMenuItemCheckIconFactory() {
        if (menuItemCheckIconFactory == null) {
            menuItemCheckIconFactory = new WindowsIconFactory$VistaMenuItemCheckIconFactory();
        }
        return menuItemCheckIconFactory;
    }
    
    public static Icon createFrameCloseIcon() {
        if (frame_closeIcon == null) {
            frame_closeIcon = new WindowsIconFactory$FrameButtonIcon(TMSchema$Part.WP_CLOSEBUTTON, null);
        }
        return frame_closeIcon;
    }
    
    public static Icon createFrameIconifyIcon() {
        if (frame_iconifyIcon == null) {
            frame_iconifyIcon = new WindowsIconFactory$FrameButtonIcon(TMSchema$Part.WP_MINBUTTON, null);
        }
        return frame_iconifyIcon;
    }
    
    public static Icon createFrameMaximizeIcon() {
        if (frame_maxIcon == null) {
            frame_maxIcon = new WindowsIconFactory$FrameButtonIcon(TMSchema$Part.WP_MAXBUTTON, null);
        }
        return frame_maxIcon;
    }
    
    public static Icon createFrameMinimizeIcon() {
        if (frame_minIcon == null) {
            frame_minIcon = new WindowsIconFactory$FrameButtonIcon(TMSchema$Part.WP_RESTOREBUTTON, null);
        }
        return frame_minIcon;
    }
    
    public static Icon createFrameResizeIcon() {
        if (frame_resizeIcon == null) frame_resizeIcon = new WindowsIconFactory$ResizeIcon(null);
        return frame_resizeIcon;
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
