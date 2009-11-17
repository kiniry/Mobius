package javax.swing.plaf.metal;

import java.awt.*;
import java.util.*;
import javax.swing.*;
import javax.swing.plaf.*;
import com.sun.java.swing.SwingUtilities2;
import sun.swing.PrintColorUIResource;

public class OceanTheme extends DefaultMetalTheme {
    
    /*synthetic*/ static Icon access$000(OceanTheme x0, String x1, UIDefaults x2) {
        return x0.getHastenedIcon(x1, x2);
    }
    private static final ColorUIResource PRIMARY1 = new ColorUIResource(6521535);
    private static final ColorUIResource PRIMARY2 = new ColorUIResource(10729676);
    private static final ColorUIResource PRIMARY3 = new ColorUIResource(12111845);
    private static final ColorUIResource SECONDARY1 = new ColorUIResource(8030873);
    private static final ColorUIResource SECONDARY2 = new ColorUIResource(12111845);
    private static final ColorUIResource SECONDARY3 = new ColorUIResource(15658734);
    private static final ColorUIResource CONTROL_TEXT_COLOR = new PrintColorUIResource(3355443, Color.BLACK);
    private static final ColorUIResource INACTIVE_CONTROL_TEXT_COLOR = new ColorUIResource(10066329);
    private static final ColorUIResource MENU_DISABLED_FOREGROUND = new ColorUIResource(10066329);
    private static final ColorUIResource OCEAN_BLACK = new PrintColorUIResource(3355443, Color.BLACK);
    {
    }
    {
    }
    
    public OceanTheme() {
        
    }
    
    public void addCustomEntriesToTable(UIDefaults table) {
        Object focusBorder = new UIDefaults$ProxyLazyValue("javax.swing.plaf.BorderUIResource$LineBorderUIResource", new Object[]{getPrimary1()});
        java.util.List buttonGradient = Arrays.asList(new Object[]{new Float(0.3F), new Float(0.0F), new ColorUIResource(14543091), getWhite(), getSecondary2()});
        Color cccccc = new ColorUIResource(13421772);
        Color dadada = new ColorUIResource(14342874);
        Color c8ddf2 = new ColorUIResource(13164018);
        Object directoryIcon = getIconResource("icons/ocean/directory.gif");
        Object fileIcon = getIconResource("icons/ocean/file.gif");
        java.util.List sliderGradient = Arrays.asList(new Object[]{new Float(0.3F), new Float(0.2F), c8ddf2, getWhite(), new ColorUIResource(SECONDARY2)});
        Object[] defaults = new Object[]{"Button.gradient", buttonGradient, "Button.rollover", Boolean.TRUE, "Button.toolBarBorderBackground", INACTIVE_CONTROL_TEXT_COLOR, "Button.disabledToolBarBorderBackground", cccccc, "Button.rolloverIconType", "ocean", "CheckBox.rollover", Boolean.TRUE, "CheckBox.gradient", buttonGradient, "CheckBoxMenuItem.gradient", buttonGradient, "FileChooser.homeFolderIcon", getIconResource("icons/ocean/homeFolder.gif"), "FileChooser.newFolderIcon", getIconResource("icons/ocean/newFolder.gif"), "FileChooser.upFolderIcon", getIconResource("icons/ocean/upFolder.gif"), "FileView.computerIcon", getIconResource("icons/ocean/computer.gif"), "FileView.directoryIcon", directoryIcon, "FileView.hardDriveIcon", getIconResource("icons/ocean/hardDrive.gif"), "FileView.fileIcon", fileIcon, "FileView.floppyDriveIcon", getIconResource("icons/ocean/floppy.gif"), "Label.disabledForeground", getInactiveControlTextColor(), "Menu.opaque", Boolean.FALSE, "MenuBar.gradient", Arrays.asList(new Object[]{new Float(1.0F), new Float(0.0F), getWhite(), dadada, new ColorUIResource(dadada)}), "MenuBar.borderColor", cccccc, "InternalFrame.activeTitleGradient", buttonGradient, "InternalFrame.closeIcon", new OceanTheme$1(this), "InternalFrame.iconifyIcon", new OceanTheme$2(this), "InternalFrame.minimizeIcon", new OceanTheme$3(this), "InternalFrame.icon", getIconResource("icons/ocean/menu.gif"), "InternalFrame.maximizeIcon", new OceanTheme$4(this), "InternalFrame.paletteCloseIcon", new OceanTheme$5(this), "List.focusCellHighlightBorder", focusBorder, "MenuBarUI", "javax.swing.plaf.metal.MetalMenuBarUI", "OptionPane.errorIcon", getIconResource("icons/ocean/error.png"), "OptionPane.informationIcon", getIconResource("icons/ocean/info.png"), "OptionPane.questionIcon", getIconResource("icons/ocean/question.png"), "OptionPane.warningIcon", getIconResource("icons/ocean/warning.png"), "RadioButton.gradient", buttonGradient, "RadioButton.rollover", Boolean.TRUE, "RadioButtonMenuItem.gradient", buttonGradient, "ScrollBar.gradient", buttonGradient, "Slider.altTrackColor", new ColorUIResource(13820655), "Slider.gradient", sliderGradient, "Slider.focusGradient", sliderGradient, "SplitPane.oneTouchButtonsOpaque", Boolean.FALSE, "SplitPane.dividerFocusColor", c8ddf2, "TabbedPane.borderHightlightColor", getPrimary1(), "TabbedPane.contentAreaColor", c8ddf2, "TabbedPane.contentBorderInsets", new Insets(4, 2, 3, 3), "TabbedPane.selected", c8ddf2, "TabbedPane.tabAreaBackground", dadada, "TabbedPane.tabAreaInsets", new Insets(2, 2, 0, 6), "TabbedPane.unselectedBackground", SECONDARY3, "Table.focusCellHighlightBorder", focusBorder, "Table.gridColor", SECONDARY1, "ToggleButton.gradient", buttonGradient, "ToolBar.borderColor", cccccc, "ToolBar.isRollover", Boolean.TRUE, "Tree.closedIcon", directoryIcon, "Tree.collapsedIcon", new OceanTheme$6(this), "Tree.expandedIcon", getIconResource("icons/ocean/expanded.gif"), "Tree.leafIcon", fileIcon, "Tree.openIcon", directoryIcon, "Tree.selectionBorderColor", getPrimary1()};
        table.putDefaults(defaults);
    }
    
    boolean isSystemTheme() {
        return true;
    }
    
    public String getName() {
        return "Ocean";
    }
    
    protected ColorUIResource getPrimary1() {
        return PRIMARY1;
    }
    
    protected ColorUIResource getPrimary2() {
        return PRIMARY2;
    }
    
    protected ColorUIResource getPrimary3() {
        return PRIMARY3;
    }
    
    protected ColorUIResource getSecondary1() {
        return SECONDARY1;
    }
    
    protected ColorUIResource getSecondary2() {
        return SECONDARY2;
    }
    
    protected ColorUIResource getSecondary3() {
        return SECONDARY3;
    }
    
    protected ColorUIResource getBlack() {
        return OCEAN_BLACK;
    }
    
    public ColorUIResource getDesktopColor() {
        return MetalTheme.white;
    }
    
    public ColorUIResource getInactiveControlTextColor() {
        return INACTIVE_CONTROL_TEXT_COLOR;
    }
    
    public ColorUIResource getControlTextColor() {
        return CONTROL_TEXT_COLOR;
    }
    
    public ColorUIResource getMenuDisabledForeground() {
        return MENU_DISABLED_FOREGROUND;
    }
    
    private Object getIconResource(String iconID) {
        return SwingUtilities2.makeIcon(getClass(), OceanTheme.class, iconID);
    }
    
    private Icon getHastenedIcon(String iconID, UIDefaults table) {
        Object res = getIconResource(iconID);
        return (Icon)(Icon)((UIDefaults$LazyValue)(UIDefaults$LazyValue)res).createValue(table);
    }
}
