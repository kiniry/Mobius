package javax.swing.plaf.metal;

import javax.swing.*;
import java.awt.*;
import java.io.Serializable;

public class MetalIconFactory implements Serializable {
    
    /*synthetic*/ static Dimension access$1900() {
        return menuCheckIconSize;
    }
    
    /*synthetic*/ static Dimension access$1800() {
        return menuArrowIconSize;
    }
    
    /*synthetic*/ static Dimension access$1700() {
        return treeControlSize;
    }
    
    /*synthetic*/ static Dimension access$1600() {
        return fileIcon16Size;
    }
    
    /*synthetic*/ static Dimension access$1500() {
        return folderIcon16Size;
    }
    {
    }
    
    public MetalIconFactory() {
        
    }
    private static Icon fileChooserDetailViewIcon;
    private static Icon fileChooserHomeFolderIcon;
    private static Icon fileChooserListViewIcon;
    private static Icon fileChooserNewFolderIcon;
    private static Icon fileChooserUpFolderIcon;
    private static Icon internalFrameAltMaximizeIcon;
    private static Icon internalFrameCloseIcon;
    private static Icon internalFrameDefaultMenuIcon;
    private static Icon internalFrameMaximizeIcon;
    private static Icon internalFrameMinimizeIcon;
    private static Icon radioButtonIcon;
    private static Icon treeComputerIcon;
    private static Icon treeFloppyDriveIcon;
    private static Icon treeHardDriveIcon;
    private static Icon menuArrowIcon;
    private static Icon menuItemArrowIcon;
    private static Icon checkBoxMenuItemIcon;
    private static Icon radioButtonMenuItemIcon;
    private static Icon checkBoxIcon;
    private static Icon oceanHorizontalSliderThumb;
    private static Icon oceanVerticalSliderThumb;
    public static final boolean DARK = false;
    public static final boolean LIGHT = true;
    
    public static Icon getFileChooserDetailViewIcon() {
        if (fileChooserDetailViewIcon == null) {
            fileChooserDetailViewIcon = new MetalIconFactory$FileChooserDetailViewIcon(null);
        }
        return fileChooserDetailViewIcon;
    }
    
    public static Icon getFileChooserHomeFolderIcon() {
        if (fileChooserHomeFolderIcon == null) {
            fileChooserHomeFolderIcon = new MetalIconFactory$FileChooserHomeFolderIcon(null);
        }
        return fileChooserHomeFolderIcon;
    }
    
    public static Icon getFileChooserListViewIcon() {
        if (fileChooserListViewIcon == null) {
            fileChooserListViewIcon = new MetalIconFactory$FileChooserListViewIcon(null);
        }
        return fileChooserListViewIcon;
    }
    
    public static Icon getFileChooserNewFolderIcon() {
        if (fileChooserNewFolderIcon == null) {
            fileChooserNewFolderIcon = new MetalIconFactory$FileChooserNewFolderIcon(null);
        }
        return fileChooserNewFolderIcon;
    }
    
    public static Icon getFileChooserUpFolderIcon() {
        if (fileChooserUpFolderIcon == null) {
            fileChooserUpFolderIcon = new MetalIconFactory$FileChooserUpFolderIcon(null);
        }
        return fileChooserUpFolderIcon;
    }
    
    public static Icon getInternalFrameAltMaximizeIcon(int size) {
        return new MetalIconFactory$InternalFrameAltMaximizeIcon(size);
    }
    
    public static Icon getInternalFrameCloseIcon(int size) {
        return new MetalIconFactory$InternalFrameCloseIcon(size);
    }
    
    public static Icon getInternalFrameDefaultMenuIcon() {
        if (internalFrameDefaultMenuIcon == null) {
            internalFrameDefaultMenuIcon = new MetalIconFactory$InternalFrameDefaultMenuIcon(null);
        }
        return internalFrameDefaultMenuIcon;
    }
    
    public static Icon getInternalFrameMaximizeIcon(int size) {
        return new MetalIconFactory$InternalFrameMaximizeIcon(size);
    }
    
    public static Icon getInternalFrameMinimizeIcon(int size) {
        return new MetalIconFactory$InternalFrameMinimizeIcon(size);
    }
    
    public static Icon getRadioButtonIcon() {
        if (radioButtonIcon == null) {
            radioButtonIcon = new MetalIconFactory$RadioButtonIcon(null);
        }
        return radioButtonIcon;
    }
    
    public static Icon getCheckBoxIcon() {
        if (checkBoxIcon == null) {
            checkBoxIcon = new MetalIconFactory$CheckBoxIcon(null);
        }
        return checkBoxIcon;
    }
    
    public static Icon getTreeComputerIcon() {
        if (treeComputerIcon == null) {
            treeComputerIcon = new MetalIconFactory$TreeComputerIcon(null);
        }
        return treeComputerIcon;
    }
    
    public static Icon getTreeFloppyDriveIcon() {
        if (treeFloppyDriveIcon == null) {
            treeFloppyDriveIcon = new MetalIconFactory$TreeFloppyDriveIcon(null);
        }
        return treeFloppyDriveIcon;
    }
    
    public static Icon getTreeFolderIcon() {
        return new MetalIconFactory$TreeFolderIcon();
    }
    
    public static Icon getTreeHardDriveIcon() {
        if (treeHardDriveIcon == null) {
            treeHardDriveIcon = new MetalIconFactory$TreeHardDriveIcon(null);
        }
        return treeHardDriveIcon;
    }
    
    public static Icon getTreeLeafIcon() {
        return new MetalIconFactory$TreeLeafIcon();
    }
    
    public static Icon getTreeControlIcon(boolean isCollapsed) {
        return new MetalIconFactory$TreeControlIcon(isCollapsed);
    }
    
    public static Icon getMenuArrowIcon() {
        if (menuArrowIcon == null) {
            menuArrowIcon = new MetalIconFactory$MenuArrowIcon(null);
        }
        return menuArrowIcon;
    }
    
    public static Icon getMenuItemCheckIcon() {
        return null;
    }
    
    public static Icon getMenuItemArrowIcon() {
        if (menuItemArrowIcon == null) {
            menuItemArrowIcon = new MetalIconFactory$MenuItemArrowIcon(null);
        }
        return menuItemArrowIcon;
    }
    
    public static Icon getCheckBoxMenuItemIcon() {
        if (checkBoxMenuItemIcon == null) {
            checkBoxMenuItemIcon = new MetalIconFactory$CheckBoxMenuItemIcon(null);
        }
        return checkBoxMenuItemIcon;
    }
    
    public static Icon getRadioButtonMenuItemIcon() {
        if (radioButtonMenuItemIcon == null) {
            radioButtonMenuItemIcon = new MetalIconFactory$RadioButtonMenuItemIcon(null);
        }
        return radioButtonMenuItemIcon;
    }
    
    public static Icon getHorizontalSliderThumbIcon() {
        if (MetalLookAndFeel.usingOcean()) {
            if (oceanHorizontalSliderThumb == null) {
                oceanHorizontalSliderThumb = new MetalIconFactory$OceanHorizontalSliderThumbIcon();
            }
            return oceanHorizontalSliderThumb;
        }
        return new MetalIconFactory$HorizontalSliderThumbIcon();
    }
    
    public static Icon getVerticalSliderThumbIcon() {
        if (MetalLookAndFeel.usingOcean()) {
            if (oceanVerticalSliderThumb == null) {
                oceanVerticalSliderThumb = new MetalIconFactory$OceanVerticalSliderThumbIcon();
            }
            return oceanVerticalSliderThumb;
        }
        return new MetalIconFactory$VerticalSliderThumbIcon();
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
    private static final Dimension folderIcon16Size = new Dimension(16, 16);
    {
    }
    {
    }
    {
    }
    private static final Dimension fileIcon16Size = new Dimension(16, 16);
    {
    }
    {
    }
    private static final Dimension treeControlSize = new Dimension(18, 18);
    {
    }
    private static final Dimension menuArrowIconSize = new Dimension(4, 8);
    private static final Dimension menuCheckIconSize = new Dimension(10, 10);
    private static final int xOff = 4;
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
