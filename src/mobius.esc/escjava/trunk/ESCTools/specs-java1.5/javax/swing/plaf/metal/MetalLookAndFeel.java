package javax.swing.plaf.metal;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import javax.swing.text.DefaultEditorKit;
import java.util.*;
import java.awt.Color;
import java.awt.event.KeyEvent;
import java.lang.reflect.*;
import java.security.AccessController;
import sun.awt.AppContext;
import sun.security.action.GetPropertyAction;
import sun.swing.SwingLazyValue;

public class MetalLookAndFeel extends BasicLookAndFeel {
    
    public MetalLookAndFeel() {
        
    }
    private static boolean METAL_LOOK_AND_FEEL_INITED = false;
    private static MetalTheme currentTheme;
    private static boolean isOnlyOneContext = true;
    private static AppContext cachedAppContext;
    private static boolean checkedWindows;
    private static boolean isWindows;
    private static boolean checkedSystemFontSettings;
    private static boolean useSystemFonts;
    
    static boolean isWindows() {
        if (!checkedWindows) {
            String osName = (String)(String)AccessController.doPrivileged(new GetPropertyAction("os.name"));
            if (osName != null && osName.indexOf("Windows") != -1) {
                isWindows = true;
                String systemFonts = (String)(String)AccessController.doPrivileged(new GetPropertyAction("swing.useSystemFontSettings"));
                useSystemFonts = (systemFonts != null && (Boolean.valueOf(systemFonts).booleanValue()));
            }
            checkedWindows = true;
        }
        return isWindows;
    }
    
    static boolean useSystemFonts() {
        if (isWindows() && useSystemFonts) {
            if (METAL_LOOK_AND_FEEL_INITED) {
                Object value = UIManager.get("Application.useSystemFontSettings");
                return (value == null || Boolean.TRUE.equals(value));
            }
            return true;
        }
        return false;
    }
    
    private static boolean useHighContrastTheme() {
        if (isWindows() && useSystemFonts()) {
            Boolean highContrast = (Boolean)(Boolean)Toolkit.getDefaultToolkit().getDesktopProperty("win.highContrast.on");
            return (highContrast == null) ? false : highContrast.booleanValue();
        }
        return false;
    }
    
    static boolean usingOcean() {
        return (getCurrentTheme() instanceof OceanTheme);
    }
    
    public String getName() {
        return "Metal";
    }
    
    public String getID() {
        return "Metal";
    }
    
    public String getDescription() {
        return "The Java(tm) Look and Feel";
    }
    
    public boolean isNativeLookAndFeel() {
        return false;
    }
    
    public boolean isSupportedLookAndFeel() {
        return true;
    }
    
    public boolean getSupportsWindowDecorations() {
        return true;
    }
    
    protected void initClassDefaults(UIDefaults table) {
        super.initClassDefaults(table);
        final String metalPackageName = "javax.swing.plaf.metal.";
        Object[] uiDefaults = {"ButtonUI", metalPackageName + "MetalButtonUI", "CheckBoxUI", metalPackageName + "MetalCheckBoxUI", "ComboBoxUI", metalPackageName + "MetalComboBoxUI", "DesktopIconUI", metalPackageName + "MetalDesktopIconUI", "FileChooserUI", metalPackageName + "MetalFileChooserUI", "InternalFrameUI", metalPackageName + "MetalInternalFrameUI", "LabelUI", metalPackageName + "MetalLabelUI", "PopupMenuSeparatorUI", metalPackageName + "MetalPopupMenuSeparatorUI", "ProgressBarUI", metalPackageName + "MetalProgressBarUI", "RadioButtonUI", metalPackageName + "MetalRadioButtonUI", "ScrollBarUI", metalPackageName + "MetalScrollBarUI", "ScrollPaneUI", metalPackageName + "MetalScrollPaneUI", "SeparatorUI", metalPackageName + "MetalSeparatorUI", "SliderUI", metalPackageName + "MetalSliderUI", "SplitPaneUI", metalPackageName + "MetalSplitPaneUI", "TabbedPaneUI", metalPackageName + "MetalTabbedPaneUI", "TextFieldUI", metalPackageName + "MetalTextFieldUI", "ToggleButtonUI", metalPackageName + "MetalToggleButtonUI", "ToolBarUI", metalPackageName + "MetalToolBarUI", "ToolTipUI", metalPackageName + "MetalToolTipUI", "TreeUI", metalPackageName + "MetalTreeUI", "RootPaneUI", metalPackageName + "MetalRootPaneUI"};
        table.putDefaults(uiDefaults);
    }
    
    protected void initSystemColorDefaults(UIDefaults table) {
        MetalTheme theme = getCurrentTheme();
        Color control = theme.getControl();
        Object[] systemColors = {"desktop", theme.getDesktopColor(), "activeCaption", theme.getWindowTitleBackground(), "activeCaptionText", theme.getWindowTitleForeground(), "activeCaptionBorder", theme.getPrimaryControlShadow(), "inactiveCaption", theme.getWindowTitleInactiveBackground(), "inactiveCaptionText", theme.getWindowTitleInactiveForeground(), "inactiveCaptionBorder", theme.getControlShadow(), "window", theme.getWindowBackground(), "windowBorder", control, "windowText", theme.getUserTextColor(), "menu", theme.getMenuBackground(), "menuText", theme.getMenuForeground(), "text", theme.getWindowBackground(), "textText", theme.getUserTextColor(), "textHighlight", theme.getTextHighlightColor(), "textHighlightText", theme.getHighlightedTextColor(), "textInactiveText", theme.getInactiveSystemTextColor(), "control", control, "controlText", theme.getControlTextColor(), "controlHighlight", theme.getControlHighlight(), "controlLtHighlight", theme.getControlHighlight(), "controlShadow", theme.getControlShadow(), "controlDkShadow", theme.getControlDarkShadow(), "scrollbar", control, "info", theme.getPrimaryControl(), "infoText", theme.getPrimaryControlInfo()};
        table.putDefaults(systemColors);
    }
    
    private void initResourceBundle(UIDefaults table) {
        table.addResourceBundle("com.sun.swing.internal.plaf.metal.resources.metal");
    }
    
    protected void initComponentDefaults(UIDefaults table) {
        super.initComponentDefaults(table);
        initResourceBundle(table);
        Color acceleratorForeground = getAcceleratorForeground();
        Color acceleratorSelectedForeground = getAcceleratorSelectedForeground();
        Color control = getControl();
        Color controlHighlight = getControlHighlight();
        Color controlShadow = getControlShadow();
        Color controlDarkShadow = getControlDarkShadow();
        Color controlTextColor = getControlTextColor();
        Color focusColor = getFocusColor();
        Color inactiveControlTextColor = getInactiveControlTextColor();
        Color menuBackground = getMenuBackground();
        Color menuSelectedBackground = getMenuSelectedBackground();
        Color menuDisabledForeground = getMenuDisabledForeground();
        Color menuSelectedForeground = getMenuSelectedForeground();
        Color primaryControl = getPrimaryControl();
        Color primaryControlDarkShadow = getPrimaryControlDarkShadow();
        Color primaryControlShadow = getPrimaryControlShadow();
        Color systemTextColor = getSystemTextColor();
        Insets zeroInsets = new InsetsUIResource(0, 0, 0, 0);
        Integer zero = new Integer(0);
        Object textFieldBorder = new SwingLazyValue("javax.swing.plaf.metal.MetalBorders", "getTextFieldBorder");
        Object dialogBorder = new MetalLookAndFeel$MetalLazyValue("javax.swing.plaf.metal.MetalBorders$DialogBorder");
        Object questionDialogBorder = new MetalLookAndFeel$MetalLazyValue("javax.swing.plaf.metal.MetalBorders$QuestionDialogBorder");
        Object fieldInputMap = new UIDefaults$LazyInputMap(new Object[]{"ctrl C", DefaultEditorKit.copyAction, "ctrl V", DefaultEditorKit.pasteAction, "ctrl X", DefaultEditorKit.cutAction, "COPY", DefaultEditorKit.copyAction, "PASTE", DefaultEditorKit.pasteAction, "CUT", DefaultEditorKit.cutAction, "shift LEFT", DefaultEditorKit.selectionBackwardAction, "shift KP_LEFT", DefaultEditorKit.selectionBackwardAction, "shift RIGHT", DefaultEditorKit.selectionForwardAction, "shift KP_RIGHT", DefaultEditorKit.selectionForwardAction, "ctrl LEFT", DefaultEditorKit.previousWordAction, "ctrl KP_LEFT", DefaultEditorKit.previousWordAction, "ctrl RIGHT", DefaultEditorKit.nextWordAction, "ctrl KP_RIGHT", DefaultEditorKit.nextWordAction, "ctrl shift LEFT", DefaultEditorKit.selectionPreviousWordAction, "ctrl shift KP_LEFT", DefaultEditorKit.selectionPreviousWordAction, "ctrl shift RIGHT", DefaultEditorKit.selectionNextWordAction, "ctrl shift KP_RIGHT", DefaultEditorKit.selectionNextWordAction, "ctrl A", DefaultEditorKit.selectAllAction, "HOME", DefaultEditorKit.beginLineAction, "END", DefaultEditorKit.endLineAction, "shift HOME", DefaultEditorKit.selectionBeginLineAction, "shift END", DefaultEditorKit.selectionEndLineAction, "BACK_SPACE", DefaultEditorKit.deletePrevCharAction, "ctrl H", DefaultEditorKit.deletePrevCharAction, "DELETE", DefaultEditorKit.deleteNextCharAction, "RIGHT", DefaultEditorKit.forwardAction, "LEFT", DefaultEditorKit.backwardAction, "KP_RIGHT", DefaultEditorKit.forwardAction, "KP_LEFT", DefaultEditorKit.backwardAction, "ENTER", JTextField.notifyAction, "ctrl BACK_SLASH", "unselect", "control shift O", "toggle-componentOrientation"});
        Object passwordInputMap = new UIDefaults$LazyInputMap(new Object[]{"ctrl C", DefaultEditorKit.copyAction, "ctrl V", DefaultEditorKit.pasteAction, "ctrl X", DefaultEditorKit.cutAction, "COPY", DefaultEditorKit.copyAction, "PASTE", DefaultEditorKit.pasteAction, "CUT", DefaultEditorKit.cutAction, "shift LEFT", DefaultEditorKit.selectionBackwardAction, "shift KP_LEFT", DefaultEditorKit.selectionBackwardAction, "shift RIGHT", DefaultEditorKit.selectionForwardAction, "shift KP_RIGHT", DefaultEditorKit.selectionForwardAction, "ctrl LEFT", DefaultEditorKit.beginLineAction, "ctrl KP_LEFT", DefaultEditorKit.beginLineAction, "ctrl RIGHT", DefaultEditorKit.endLineAction, "ctrl KP_RIGHT", DefaultEditorKit.endLineAction, "ctrl shift LEFT", DefaultEditorKit.selectionBeginLineAction, "ctrl shift KP_LEFT", DefaultEditorKit.selectionBeginLineAction, "ctrl shift RIGHT", DefaultEditorKit.selectionEndLineAction, "ctrl shift KP_RIGHT", DefaultEditorKit.selectionEndLineAction, "ctrl A", DefaultEditorKit.selectAllAction, "HOME", DefaultEditorKit.beginLineAction, "END", DefaultEditorKit.endLineAction, "shift HOME", DefaultEditorKit.selectionBeginLineAction, "shift END", DefaultEditorKit.selectionEndLineAction, "BACK_SPACE", DefaultEditorKit.deletePrevCharAction, "ctrl H", DefaultEditorKit.deletePrevCharAction, "DELETE", DefaultEditorKit.deleteNextCharAction, "RIGHT", DefaultEditorKit.forwardAction, "LEFT", DefaultEditorKit.backwardAction, "KP_RIGHT", DefaultEditorKit.forwardAction, "KP_LEFT", DefaultEditorKit.backwardAction, "ENTER", JTextField.notifyAction, "ctrl BACK_SLASH", "unselect", "control shift O", "toggle-componentOrientation"});
        Object multilineInputMap = new UIDefaults$LazyInputMap(new Object[]{"ctrl C", DefaultEditorKit.copyAction, "ctrl V", DefaultEditorKit.pasteAction, "ctrl X", DefaultEditorKit.cutAction, "COPY", DefaultEditorKit.copyAction, "PASTE", DefaultEditorKit.pasteAction, "CUT", DefaultEditorKit.cutAction, "shift LEFT", DefaultEditorKit.selectionBackwardAction, "shift KP_LEFT", DefaultEditorKit.selectionBackwardAction, "shift RIGHT", DefaultEditorKit.selectionForwardAction, "shift KP_RIGHT", DefaultEditorKit.selectionForwardAction, "ctrl LEFT", DefaultEditorKit.previousWordAction, "ctrl KP_LEFT", DefaultEditorKit.previousWordAction, "ctrl RIGHT", DefaultEditorKit.nextWordAction, "ctrl KP_RIGHT", DefaultEditorKit.nextWordAction, "ctrl shift LEFT", DefaultEditorKit.selectionPreviousWordAction, "ctrl shift KP_LEFT", DefaultEditorKit.selectionPreviousWordAction, "ctrl shift RIGHT", DefaultEditorKit.selectionNextWordAction, "ctrl shift KP_RIGHT", DefaultEditorKit.selectionNextWordAction, "ctrl A", DefaultEditorKit.selectAllAction, "HOME", DefaultEditorKit.beginLineAction, "END", DefaultEditorKit.endLineAction, "shift HOME", DefaultEditorKit.selectionBeginLineAction, "shift END", DefaultEditorKit.selectionEndLineAction, "UP", DefaultEditorKit.upAction, "KP_UP", DefaultEditorKit.upAction, "DOWN", DefaultEditorKit.downAction, "KP_DOWN", DefaultEditorKit.downAction, "PAGE_UP", DefaultEditorKit.pageUpAction, "PAGE_DOWN", DefaultEditorKit.pageDownAction, "shift PAGE_UP", "selection-page-up", "shift PAGE_DOWN", "selection-page-down", "ctrl shift PAGE_UP", "selection-page-left", "ctrl shift PAGE_DOWN", "selection-page-right", "shift UP", DefaultEditorKit.selectionUpAction, "shift KP_UP", DefaultEditorKit.selectionUpAction, "shift DOWN", DefaultEditorKit.selectionDownAction, "shift KP_DOWN", DefaultEditorKit.selectionDownAction, "ENTER", DefaultEditorKit.insertBreakAction, "BACK_SPACE", DefaultEditorKit.deletePrevCharAction, "ctrl H", DefaultEditorKit.deletePrevCharAction, "DELETE", DefaultEditorKit.deleteNextCharAction, "RIGHT", DefaultEditorKit.forwardAction, "LEFT", DefaultEditorKit.backwardAction, "KP_RIGHT", DefaultEditorKit.forwardAction, "KP_LEFT", DefaultEditorKit.backwardAction, "TAB", DefaultEditorKit.insertTabAction, "ctrl BACK_SLASH", "unselect", "ctrl HOME", DefaultEditorKit.beginAction, "ctrl END", DefaultEditorKit.endAction, "ctrl shift HOME", DefaultEditorKit.selectionBeginAction, "ctrl shift END", DefaultEditorKit.selectionEndAction, "ctrl T", "next-link-action", "ctrl shift T", "previous-link-action", "ctrl SPACE", "activate-link-action", "control shift O", "toggle-componentOrientation"});
        Object scrollPaneBorder = new SwingLazyValue("javax.swing.plaf.metal.MetalBorders$ScrollPaneBorder");
        Object buttonBorder = new SwingLazyValue("javax.swing.plaf.metal.MetalBorders", "getButtonBorder");
        Object toggleButtonBorder = new SwingLazyValue("javax.swing.plaf.metal.MetalBorders", "getToggleButtonBorder");
        Object titledBorderBorder = new SwingLazyValue("javax.swing.plaf.BorderUIResource$LineBorderUIResource", new Object[]{controlShadow});
        Object desktopIconBorder = new SwingLazyValue("javax.swing.plaf.metal.MetalBorders", "getDesktopIconBorder");
        Object menuBarBorder = new SwingLazyValue("javax.swing.plaf.metal.MetalBorders$MenuBarBorder");
        Object popupMenuBorder = new SwingLazyValue("javax.swing.plaf.metal.MetalBorders$PopupMenuBorder");
        Object menuItemBorder = new SwingLazyValue("javax.swing.plaf.metal.MetalBorders$MenuItemBorder");
        Object menuItemAcceleratorDelimiter = new String("-");
        Object toolBarBorder = new SwingLazyValue("javax.swing.plaf.metal.MetalBorders$ToolBarBorder");
        Object progressBarBorder = new SwingLazyValue("javax.swing.plaf.BorderUIResource$LineBorderUIResource", new Object[]{controlDarkShadow, new Integer(1)});
        Object toolTipBorder = new SwingLazyValue("javax.swing.plaf.BorderUIResource$LineBorderUIResource", new Object[]{primaryControlDarkShadow});
        Object toolTipBorderInactive = new SwingLazyValue("javax.swing.plaf.BorderUIResource$LineBorderUIResource", new Object[]{controlDarkShadow});
        Object focusCellHighlightBorder = new SwingLazyValue("javax.swing.plaf.BorderUIResource$LineBorderUIResource", new Object[]{focusColor});
        Object tabbedPaneTabAreaInsets = new InsetsUIResource(4, 2, 0, 6);
        Object tabbedPaneTabInsets = new InsetsUIResource(0, 9, 1, 9);
        final Object[] internalFrameIconArgs = new Object[1];
        internalFrameIconArgs[0] = new Integer(16);
        Object[] defaultCueList = new Object[]{"OptionPane.errorSound", "OptionPane.informationSound", "OptionPane.questionSound", "OptionPane.warningSound"};
        MetalTheme theme = getCurrentTheme();
        Object menuTextValue = new MetalLookAndFeel$FontActiveValue(theme, MetalTheme.MENU_TEXT_FONT);
        Object controlTextValue = new MetalLookAndFeel$FontActiveValue(theme, MetalTheme.CONTROL_TEXT_FONT);
        Object userTextValue = new MetalLookAndFeel$FontActiveValue(theme, MetalTheme.USER_TEXT_FONT);
        Object windowTitleValue = new MetalLookAndFeel$FontActiveValue(theme, MetalTheme.WINDOW_TITLE_FONT);
        Object subTextValue = new MetalLookAndFeel$FontActiveValue(theme, MetalTheme.SUB_TEXT_FONT);
        Object systemTextValue = new MetalLookAndFeel$FontActiveValue(theme, MetalTheme.SYSTEM_TEXT_FONT);
        Object[] defaults = {"AuditoryCues.defaultCueList", defaultCueList, "AuditoryCues.playList", null, "TextField.border", textFieldBorder, "TextField.font", userTextValue, "PasswordField.border", textFieldBorder, "PasswordField.font", userTextValue, "TextArea.font", userTextValue, "TextPane.background", table.get("window"), "TextPane.font", userTextValue, "EditorPane.background", table.get("window"), "EditorPane.font", userTextValue, "TextField.focusInputMap", fieldInputMap, "PasswordField.focusInputMap", passwordInputMap, "TextArea.focusInputMap", multilineInputMap, "TextPane.focusInputMap", multilineInputMap, "EditorPane.focusInputMap", multilineInputMap, "FormattedTextField.border", textFieldBorder, "FormattedTextField.font", userTextValue, "FormattedTextField.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"ctrl C", DefaultEditorKit.copyAction, "ctrl V", DefaultEditorKit.pasteAction, "ctrl X", DefaultEditorKit.cutAction, "COPY", DefaultEditorKit.copyAction, "PASTE", DefaultEditorKit.pasteAction, "CUT", DefaultEditorKit.cutAction, "shift LEFT", DefaultEditorKit.selectionBackwardAction, "shift KP_LEFT", DefaultEditorKit.selectionBackwardAction, "shift RIGHT", DefaultEditorKit.selectionForwardAction, "shift KP_RIGHT", DefaultEditorKit.selectionForwardAction, "ctrl LEFT", DefaultEditorKit.previousWordAction, "ctrl KP_LEFT", DefaultEditorKit.previousWordAction, "ctrl RIGHT", DefaultEditorKit.nextWordAction, "ctrl KP_RIGHT", DefaultEditorKit.nextWordAction, "ctrl shift LEFT", DefaultEditorKit.selectionPreviousWordAction, "ctrl shift KP_LEFT", DefaultEditorKit.selectionPreviousWordAction, "ctrl shift RIGHT", DefaultEditorKit.selectionNextWordAction, "ctrl shift KP_RIGHT", DefaultEditorKit.selectionNextWordAction, "ctrl A", DefaultEditorKit.selectAllAction, "HOME", DefaultEditorKit.beginLineAction, "END", DefaultEditorKit.endLineAction, "shift HOME", DefaultEditorKit.selectionBeginLineAction, "shift END", DefaultEditorKit.selectionEndLineAction, "BACK_SPACE", DefaultEditorKit.deletePrevCharAction, "ctrl H", DefaultEditorKit.deletePrevCharAction, "DELETE", DefaultEditorKit.deleteNextCharAction, "RIGHT", DefaultEditorKit.forwardAction, "LEFT", DefaultEditorKit.backwardAction, "KP_RIGHT", DefaultEditorKit.forwardAction, "KP_LEFT", DefaultEditorKit.backwardAction, "ENTER", JTextField.notifyAction, "ctrl BACK_SLASH", "unselect", "control shift O", "toggle-componentOrientation", "ESCAPE", "reset-field-edit", "UP", "increment", "KP_UP", "increment", "DOWN", "decrement", "KP_DOWN", "decrement"}), "Button.defaultButtonFollowsFocus", Boolean.FALSE, "Button.disabledText", inactiveControlTextColor, "Button.select", controlShadow, "Button.border", buttonBorder, "Button.font", controlTextValue, "Button.focus", focusColor, "Button.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"SPACE", "pressed", "released SPACE", "released"}), "CheckBox.disabledText", inactiveControlTextColor, "Checkbox.select", controlShadow, "CheckBox.font", controlTextValue, "CheckBox.focus", focusColor, "CheckBox.icon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getCheckBoxIcon"), "CheckBox.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"SPACE", "pressed", "released SPACE", "released"}), "RadioButton.disabledText", inactiveControlTextColor, "RadioButton.select", controlShadow, "RadioButton.icon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getRadioButtonIcon"), "RadioButton.font", controlTextValue, "RadioButton.focus", focusColor, "RadioButton.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"SPACE", "pressed", "released SPACE", "released"}), "ToggleButton.select", controlShadow, "ToggleButton.disabledText", inactiveControlTextColor, "ToggleButton.focus", focusColor, "ToggleButton.border", toggleButtonBorder, "ToggleButton.font", controlTextValue, "ToggleButton.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"SPACE", "pressed", "released SPACE", "released"}), "FileView.directoryIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getTreeFolderIcon"), "FileView.fileIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getTreeLeafIcon"), "FileView.computerIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getTreeComputerIcon"), "FileView.hardDriveIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getTreeHardDriveIcon"), "FileView.floppyDriveIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getTreeFloppyDriveIcon"), "FileChooser.detailsViewIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getFileChooserDetailViewIcon"), "FileChooser.homeFolderIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getFileChooserHomeFolderIcon"), "FileChooser.listViewIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getFileChooserListViewIcon"), "FileChooser.newFolderIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getFileChooserNewFolderIcon"), "FileChooser.upFolderIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getFileChooserUpFolderIcon"), "FileChooser.lookInLabelMnemonic", new Integer(KeyEvent.VK_I), "FileChooser.fileNameLabelMnemonic", new Integer(KeyEvent.VK_N), "FileChooser.filesOfTypeLabelMnemonic", new Integer(KeyEvent.VK_T), "FileChooser.usesSingleFilePane", Boolean.TRUE, "FileChooser.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"ESCAPE", "cancelSelection", "F2", "editFileName", "F5", "refresh", "BACK_SPACE", "Go Up", "ENTER", "approveSelection"}), "ToolTip.font", systemTextValue, "ToolTip.border", toolTipBorder, "ToolTip.borderInactive", toolTipBorderInactive, "ToolTip.backgroundInactive", control, "ToolTip.foregroundInactive", controlDarkShadow, "ToolTip.hideAccelerator", Boolean.FALSE, "Slider.border", null, "Slider.foreground", primaryControlShadow, "Slider.focus", focusColor, "Slider.focusInsets", zeroInsets, "Slider.trackWidth", new Integer(7), "Slider.majorTickLength", new Integer(6), "Slider.horizontalThumbIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getHorizontalSliderThumbIcon"), "Slider.verticalThumbIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getVerticalSliderThumbIcon"), "Slider.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"RIGHT", "positiveUnitIncrement", "KP_RIGHT", "positiveUnitIncrement", "DOWN", "negativeUnitIncrement", "KP_DOWN", "negativeUnitIncrement", "PAGE_DOWN", "negativeBlockIncrement", "ctrl PAGE_DOWN", "negativeBlockIncrement", "LEFT", "negativeUnitIncrement", "KP_LEFT", "negativeUnitIncrement", "UP", "positiveUnitIncrement", "KP_UP", "positiveUnitIncrement", "PAGE_UP", "positiveBlockIncrement", "ctrl PAGE_UP", "positiveBlockIncrement", "HOME", "minScroll", "END", "maxScroll"}), "ProgressBar.font", controlTextValue, "ProgressBar.foreground", primaryControlShadow, "ProgressBar.selectionBackground", primaryControlDarkShadow, "ProgressBar.border", progressBarBorder, "ProgressBar.cellSpacing", zero, "ProgressBar.cellLength", new Integer(1), "ComboBox.background", control, "ComboBox.foreground", controlTextColor, "ComboBox.selectionBackground", primaryControlShadow, "ComboBox.selectionForeground", controlTextColor, "ComboBox.font", controlTextValue, "ComboBox.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"ESCAPE", "hidePopup", "PAGE_UP", "pageUpPassThrough", "PAGE_DOWN", "pageDownPassThrough", "HOME", "homePassThrough", "END", "endPassThrough", "DOWN", "selectNext", "KP_DOWN", "selectNext", "alt DOWN", "togglePopup", "alt KP_DOWN", "togglePopup", "alt UP", "togglePopup", "alt KP_UP", "togglePopup", "SPACE", "spacePopup", "ENTER", "enterPressed", "UP", "selectPrevious", "KP_UP", "selectPrevious"}), "InternalFrame.icon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getInternalFrameDefaultMenuIcon"), "InternalFrame.border", new SwingLazyValue("javax.swing.plaf.metal.MetalBorders$InternalFrameBorder"), "InternalFrame.optionDialogBorder", new SwingLazyValue("javax.swing.plaf.metal.MetalBorders$OptionDialogBorder"), "InternalFrame.paletteBorder", new SwingLazyValue("javax.swing.plaf.metal.MetalBorders$PaletteBorder"), "InternalFrame.paletteTitleHeight", new Integer(11), "InternalFrame.paletteCloseIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory$PaletteCloseIcon"), "InternalFrame.closeIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getInternalFrameCloseIcon", internalFrameIconArgs), "InternalFrame.maximizeIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getInternalFrameMaximizeIcon", internalFrameIconArgs), "InternalFrame.iconifyIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getInternalFrameMinimizeIcon", internalFrameIconArgs), "InternalFrame.minimizeIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getInternalFrameAltMaximizeIcon", internalFrameIconArgs), "InternalFrame.titleFont", windowTitleValue, "InternalFrame.windowBindings", null, "InternalFrame.closeSound", "sounds/FrameClose.wav", "InternalFrame.maximizeSound", "sounds/FrameMaximize.wav", "InternalFrame.minimizeSound", "sounds/FrameMinimize.wav", "InternalFrame.restoreDownSound", "sounds/FrameRestoreDown.wav", "InternalFrame.restoreUpSound", "sounds/FrameRestoreUp.wav", "DesktopIcon.border", desktopIconBorder, "DesktopIcon.font", controlTextValue, "DesktopIcon.foreground", controlTextColor, "DesktopIcon.background", control, "DesktopIcon.width", new Integer(160), "Desktop.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"ctrl F5", "restore", "ctrl F4", "close", "ctrl F7", "move", "ctrl F8", "resize", "RIGHT", "right", "KP_RIGHT", "right", "shift RIGHT", "shrinkRight", "shift KP_RIGHT", "shrinkRight", "LEFT", "left", "KP_LEFT", "left", "shift LEFT", "shrinkLeft", "shift KP_LEFT", "shrinkLeft", "UP", "up", "KP_UP", "up", "shift UP", "shrinkUp", "shift KP_UP", "shrinkUp", "DOWN", "down", "KP_DOWN", "down", "shift DOWN", "shrinkDown", "shift KP_DOWN", "shrinkDown", "ESCAPE", "escape", "ctrl F9", "minimize", "ctrl F10", "maximize", "ctrl F6", "selectNextFrame", "ctrl TAB", "selectNextFrame", "ctrl alt F6", "selectNextFrame", "shift ctrl alt F6", "selectPreviousFrame", "ctrl F12", "navigateNext", "shift ctrl F12", "navigatePrevious"}), "TitledBorder.font", controlTextValue, "TitledBorder.titleColor", systemTextColor, "TitledBorder.border", titledBorderBorder, "Label.font", controlTextValue, "Label.foreground", systemTextColor, "Label.disabledForeground", getInactiveSystemTextColor(), "List.font", controlTextValue, "List.focusCellHighlightBorder", focusCellHighlightBorder, "List.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"ctrl C", "copy", "ctrl V", "paste", "ctrl X", "cut", "COPY", "copy", "PASTE", "paste", "CUT", "cut", "UP", "selectPreviousRow", "KP_UP", "selectPreviousRow", "shift UP", "selectPreviousRowExtendSelection", "shift KP_UP", "selectPreviousRowExtendSelection", "ctrl shift UP", "selectPreviousRowExtendSelection", "ctrl shift KP_UP", "selectPreviousRowExtendSelection", "ctrl UP", "selectPreviousRowChangeLead", "ctrl KP_UP", "selectPreviousRowChangeLead", "DOWN", "selectNextRow", "KP_DOWN", "selectNextRow", "shift DOWN", "selectNextRowExtendSelection", "shift KP_DOWN", "selectNextRowExtendSelection", "ctrl shift DOWN", "selectNextRowExtendSelection", "ctrl shift KP_DOWN", "selectNextRowExtendSelection", "ctrl DOWN", "selectNextRowChangeLead", "ctrl KP_DOWN", "selectNextRowChangeLead", "LEFT", "selectPreviousColumn", "KP_LEFT", "selectPreviousColumn", "shift LEFT", "selectPreviousColumnExtendSelection", "shift KP_LEFT", "selectPreviousColumnExtendSelection", "ctrl shift LEFT", "selectPreviousColumnExtendSelection", "ctrl shift KP_LEFT", "selectPreviousColumnExtendSelection", "ctrl LEFT", "selectPreviousColumnChangeLead", "ctrl KP_LEFT", "selectPreviousColumnChangeLead", "RIGHT", "selectNextColumn", "KP_RIGHT", "selectNextColumn", "shift RIGHT", "selectNextColumnExtendSelection", "shift KP_RIGHT", "selectNextColumnExtendSelection", "ctrl shift RIGHT", "selectNextColumnExtendSelection", "ctrl shift KP_RIGHT", "selectNextColumnExtendSelection", "ctrl RIGHT", "selectNextColumnChangeLead", "ctrl KP_RIGHT", "selectNextColumnChangeLead", "HOME", "selectFirstRow", "shift HOME", "selectFirstRowExtendSelection", "ctrl shift HOME", "selectFirstRowExtendSelection", "ctrl HOME", "selectFirstRowChangeLead", "END", "selectLastRow", "shift END", "selectLastRowExtendSelection", "ctrl shift END", "selectLastRowExtendSelection", "ctrl END", "selectLastRowChangeLead", "PAGE_UP", "scrollUp", "shift PAGE_UP", "scrollUpExtendSelection", "ctrl shift PAGE_UP", "scrollUpExtendSelection", "ctrl PAGE_UP", "scrollUpChangeLead", "PAGE_DOWN", "scrollDown", "shift PAGE_DOWN", "scrollDownExtendSelection", "ctrl shift PAGE_DOWN", "scrollDownExtendSelection", "ctrl PAGE_DOWN", "scrollDownChangeLead", "ctrl A", "selectAll", "ctrl SLASH", "selectAll", "ctrl BACK_SLASH", "clearSelection", "SPACE", "addToSelection", "ctrl SPACE", "toggleAndAnchor", "shift SPACE", "extendTo", "ctrl shift SPACE", "moveSelectionTo"}), "ScrollBar.background", control, "ScrollBar.highlight", controlHighlight, "ScrollBar.shadow", controlShadow, "ScrollBar.darkShadow", controlDarkShadow, "ScrollBar.thumb", primaryControlShadow, "ScrollBar.thumbShadow", primaryControlDarkShadow, "ScrollBar.thumbHighlight", primaryControl, "ScrollBar.width", new Integer(17), "ScrollBar.allowsAbsolutePositioning", Boolean.TRUE, "ScrollBar.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"RIGHT", "positiveUnitIncrement", "KP_RIGHT", "positiveUnitIncrement", "DOWN", "positiveUnitIncrement", "KP_DOWN", "positiveUnitIncrement", "PAGE_DOWN", "positiveBlockIncrement", "LEFT", "negativeUnitIncrement", "KP_LEFT", "negativeUnitIncrement", "UP", "negativeUnitIncrement", "KP_UP", "negativeUnitIncrement", "PAGE_UP", "negativeBlockIncrement", "HOME", "minScroll", "END", "maxScroll"}), "ScrollPane.border", scrollPaneBorder, "ScrollPane.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"RIGHT", "unitScrollRight", "KP_RIGHT", "unitScrollRight", "DOWN", "unitScrollDown", "KP_DOWN", "unitScrollDown", "LEFT", "unitScrollLeft", "KP_LEFT", "unitScrollLeft", "UP", "unitScrollUp", "KP_UP", "unitScrollUp", "PAGE_UP", "scrollUp", "PAGE_DOWN", "scrollDown", "ctrl PAGE_UP", "scrollLeft", "ctrl PAGE_DOWN", "scrollRight", "ctrl HOME", "scrollHome", "ctrl END", "scrollEnd"}), "TabbedPane.font", controlTextValue, "TabbedPane.tabAreaBackground", control, "TabbedPane.background", controlShadow, "TabbedPane.light", control, "TabbedPane.focus", primaryControlDarkShadow, "TabbedPane.selected", control, "TabbedPane.selectHighlight", controlHighlight, "TabbedPane.tabAreaInsets", tabbedPaneTabAreaInsets, "TabbedPane.tabInsets", tabbedPaneTabInsets, "TabbedPane.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"RIGHT", "navigateRight", "KP_RIGHT", "navigateRight", "LEFT", "navigateLeft", "KP_LEFT", "navigateLeft", "UP", "navigateUp", "KP_UP", "navigateUp", "DOWN", "navigateDown", "KP_DOWN", "navigateDown", "ctrl DOWN", "requestFocusForVisibleComponent", "ctrl KP_DOWN", "requestFocusForVisibleComponent"}), "TabbedPane.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"ctrl PAGE_DOWN", "navigatePageDown", "ctrl PAGE_UP", "navigatePageUp", "ctrl UP", "requestFocus", "ctrl KP_UP", "requestFocus"}), "Table.font", userTextValue, "Table.focusCellHighlightBorder", focusCellHighlightBorder, "Table.scrollPaneBorder", scrollPaneBorder, "Table.gridColor", controlShadow, "Table.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"ctrl C", "copy", "ctrl V", "paste", "ctrl X", "cut", "COPY", "copy", "PASTE", "paste", "CUT", "cut", "RIGHT", "selectNextColumn", "KP_RIGHT", "selectNextColumn", "shift RIGHT", "selectNextColumnExtendSelection", "shift KP_RIGHT", "selectNextColumnExtendSelection", "ctrl shift RIGHT", "selectNextColumnExtendSelection", "ctrl shift KP_RIGHT", "selectNextColumnExtendSelection", "ctrl RIGHT", "selectNextColumnChangeLead", "ctrl KP_RIGHT", "selectNextColumnChangeLead", "LEFT", "selectPreviousColumn", "KP_LEFT", "selectPreviousColumn", "shift LEFT", "selectPreviousColumnExtendSelection", "shift KP_LEFT", "selectPreviousColumnExtendSelection", "ctrl shift LEFT", "selectPreviousColumnExtendSelection", "ctrl shift KP_LEFT", "selectPreviousColumnExtendSelection", "ctrl LEFT", "selectPreviousColumnChangeLead", "ctrl KP_LEFT", "selectPreviousColumnChangeLead", "DOWN", "selectNextRow", "KP_DOWN", "selectNextRow", "shift DOWN", "selectNextRowExtendSelection", "shift KP_DOWN", "selectNextRowExtendSelection", "ctrl shift DOWN", "selectNextRowExtendSelection", "ctrl shift KP_DOWN", "selectNextRowExtendSelection", "ctrl DOWN", "selectNextRowChangeLead", "ctrl KP_DOWN", "selectNextRowChangeLead", "UP", "selectPreviousRow", "KP_UP", "selectPreviousRow", "shift UP", "selectPreviousRowExtendSelection", "shift KP_UP", "selectPreviousRowExtendSelection", "ctrl shift UP", "selectPreviousRowExtendSelection", "ctrl shift KP_UP", "selectPreviousRowExtendSelection", "ctrl UP", "selectPreviousRowChangeLead", "ctrl KP_UP", "selectPreviousRowChangeLead", "HOME", "selectFirstColumn", "shift HOME", "selectFirstColumnExtendSelection", "ctrl shift HOME", "selectFirstRowExtendSelection", "ctrl HOME", "selectFirstRow", "END", "selectLastColumn", "shift END", "selectLastColumnExtendSelection", "ctrl shift END", "selectLastRowExtendSelection", "ctrl END", "selectLastRow", "PAGE_UP", "scrollUpChangeSelection", "shift PAGE_UP", "scrollUpExtendSelection", "ctrl shift PAGE_UP", "scrollLeftExtendSelection", "ctrl PAGE_UP", "scrollLeftChangeSelection", "PAGE_DOWN", "scrollDownChangeSelection", "shift PAGE_DOWN", "scrollDownExtendSelection", "ctrl shift PAGE_DOWN", "scrollRightExtendSelection", "ctrl PAGE_DOWN", "scrollRightChangeSelection", "TAB", "selectNextColumnCell", "shift TAB", "selectPreviousColumnCell", "ENTER", "selectNextRowCell", "shift ENTER", "selectPreviousRowCell", "ctrl A", "selectAll", "ctrl SLASH", "selectAll", "ctrl BACK_SLASH", "clearSelection", "ESCAPE", "cancel", "F2", "startEditing", "SPACE", "addToSelection", "ctrl SPACE", "toggleAndAnchor", "shift SPACE", "extendTo", "ctrl shift SPACE", "moveSelectionTo"}), "TableHeader.font", userTextValue, "TableHeader.cellBorder", new SwingLazyValue("javax.swing.plaf.metal.MetalBorders$TableHeaderBorder"), "MenuBar.border", menuBarBorder, "MenuBar.font", menuTextValue, "MenuBar.windowBindings", new Object[]{"F10", "takeFocus"}, "Menu.border", menuItemBorder, "Menu.borderPainted", Boolean.TRUE, "Menu.menuPopupOffsetX", zero, "Menu.menuPopupOffsetY", zero, "Menu.submenuPopupOffsetX", new Integer(-4), "Menu.submenuPopupOffsetY", new Integer(-3), "Menu.font", menuTextValue, "Menu.selectionForeground", menuSelectedForeground, "Menu.selectionBackground", menuSelectedBackground, "Menu.disabledForeground", menuDisabledForeground, "Menu.acceleratorFont", subTextValue, "Menu.acceleratorForeground", acceleratorForeground, "Menu.acceleratorSelectionForeground", acceleratorSelectedForeground, "Menu.checkIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getMenuItemCheckIcon"), "Menu.arrowIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getMenuArrowIcon"), "MenuItem.border", menuItemBorder, "MenuItem.borderPainted", Boolean.TRUE, "MenuItem.font", menuTextValue, "MenuItem.selectionForeground", menuSelectedForeground, "MenuItem.selectionBackground", menuSelectedBackground, "MenuItem.disabledForeground", menuDisabledForeground, "MenuItem.acceleratorFont", subTextValue, "MenuItem.acceleratorForeground", acceleratorForeground, "MenuItem.acceleratorSelectionForeground", acceleratorSelectedForeground, "MenuItem.acceleratorDelimiter", menuItemAcceleratorDelimiter, "MenuItem.checkIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getMenuItemCheckIcon"), "MenuItem.arrowIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getMenuItemArrowIcon"), "MenuItem.commandSound", "sounds/MenuItemCommand.wav", "OptionPane.windowBindings", new Object[]{"ESCAPE", "close"}, "OptionPane.informationSound", "sounds/OptionPaneInformation.wav", "OptionPane.warningSound", "sounds/OptionPaneWarning.wav", "OptionPane.errorSound", "sounds/OptionPaneError.wav", "OptionPane.questionSound", "sounds/OptionPaneQuestion.wav", "OptionPane.errorDialog.border.background", new ColorUIResource(153, 51, 51), "OptionPane.errorDialog.titlePane.foreground", new ColorUIResource(51, 0, 0), "OptionPane.errorDialog.titlePane.background", new ColorUIResource(255, 153, 153), "OptionPane.errorDialog.titlePane.shadow", new ColorUIResource(204, 102, 102), "OptionPane.questionDialog.border.background", new ColorUIResource(51, 102, 51), "OptionPane.questionDialog.titlePane.foreground", new ColorUIResource(0, 51, 0), "OptionPane.questionDialog.titlePane.background", new ColorUIResource(153, 204, 153), "OptionPane.questionDialog.titlePane.shadow", new ColorUIResource(102, 153, 102), "OptionPane.warningDialog.border.background", new ColorUIResource(153, 102, 51), "OptionPane.warningDialog.titlePane.foreground", new ColorUIResource(102, 51, 0), "OptionPane.warningDialog.titlePane.background", new ColorUIResource(255, 204, 153), "OptionPane.warningDialog.titlePane.shadow", new ColorUIResource(204, 153, 102), "Separator.background", getSeparatorBackground(), "Separator.foreground", getSeparatorForeground(), "PopupMenu.border", popupMenuBorder, "PopupMenu.popupSound", "sounds/PopupMenuPopup.wav", "PopupMenu.font", menuTextValue, "CheckBoxMenuItem.border", menuItemBorder, "CheckBoxMenuItem.borderPainted", Boolean.TRUE, "CheckBoxMenuItem.font", menuTextValue, "CheckBoxMenuItem.selectionForeground", menuSelectedForeground, "CheckBoxMenuItem.selectionBackground", menuSelectedBackground, "CheckBoxMenuItem.disabledForeground", menuDisabledForeground, "CheckBoxMenuItem.acceleratorFont", subTextValue, "CheckBoxMenuItem.acceleratorForeground", acceleratorForeground, "CheckBoxMenuItem.acceleratorSelectionForeground", acceleratorSelectedForeground, "CheckBoxMenuItem.checkIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getCheckBoxMenuItemIcon"), "CheckBoxMenuItem.arrowIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getMenuItemArrowIcon"), "CheckBoxMenuItem.commandSound", "sounds/MenuItemCommand.wav", "RadioButtonMenuItem.border", menuItemBorder, "RadioButtonMenuItem.borderPainted", Boolean.TRUE, "RadioButtonMenuItem.font", menuTextValue, "RadioButtonMenuItem.selectionForeground", menuSelectedForeground, "RadioButtonMenuItem.selectionBackground", menuSelectedBackground, "RadioButtonMenuItem.disabledForeground", menuDisabledForeground, "RadioButtonMenuItem.acceleratorFont", subTextValue, "RadioButtonMenuItem.acceleratorForeground", acceleratorForeground, "RadioButtonMenuItem.acceleratorSelectionForeground", acceleratorSelectedForeground, "RadioButtonMenuItem.checkIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getRadioButtonMenuItemIcon"), "RadioButtonMenuItem.arrowIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getMenuItemArrowIcon"), "RadioButtonMenuItem.commandSound", "sounds/MenuItemCommand.wav", "Spinner.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"UP", "increment", "KP_UP", "increment", "DOWN", "decrement", "KP_DOWN", "decrement"}), "Spinner.arrowButtonInsets", zeroInsets, "Spinner.border", textFieldBorder, "Spinner.arrowButtonBorder", buttonBorder, "Spinner.font", controlTextValue, "SplitPane.dividerSize", new Integer(10), "SplitPane.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"UP", "negativeIncrement", "DOWN", "positiveIncrement", "LEFT", "negativeIncrement", "RIGHT", "positiveIncrement", "KP_UP", "negativeIncrement", "KP_DOWN", "positiveIncrement", "KP_LEFT", "negativeIncrement", "KP_RIGHT", "positiveIncrement", "HOME", "selectMin", "END", "selectMax", "F8", "startResize", "F6", "toggleFocus", "ctrl TAB", "focusOutForward", "ctrl shift TAB", "focusOutBackward"}), "SplitPane.centerOneTouchButtons", Boolean.FALSE, "SplitPane.dividerFocusColor", primaryControl, "Tree.font", userTextValue, "Tree.textBackground", getWindowBackground(), "Tree.selectionBorderColor", focusColor, "Tree.openIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getTreeFolderIcon"), "Tree.closedIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getTreeFolderIcon"), "Tree.leafIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getTreeLeafIcon"), "Tree.expandedIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getTreeControlIcon", new Object[]{Boolean.valueOf(MetalIconFactory.DARK)}), "Tree.collapsedIcon", new SwingLazyValue("javax.swing.plaf.metal.MetalIconFactory", "getTreeControlIcon", new Object[]{Boolean.valueOf(MetalIconFactory.LIGHT)}), "Tree.line", primaryControl, "Tree.hash", primaryControl, "Tree.rowHeight", zero, "Tree.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"ADD", "expand", "SUBTRACT", "collapse", "ctrl C", "copy", "ctrl V", "paste", "ctrl X", "cut", "COPY", "copy", "PASTE", "paste", "CUT", "cut", "UP", "selectPrevious", "KP_UP", "selectPrevious", "shift UP", "selectPreviousExtendSelection", "shift KP_UP", "selectPreviousExtendSelection", "ctrl shift UP", "selectPreviousExtendSelection", "ctrl shift KP_UP", "selectPreviousExtendSelection", "ctrl UP", "selectPreviousChangeLead", "ctrl KP_UP", "selectPreviousChangeLead", "DOWN", "selectNext", "KP_DOWN", "selectNext", "shift DOWN", "selectNextExtendSelection", "shift KP_DOWN", "selectNextExtendSelection", "ctrl shift DOWN", "selectNextExtendSelection", "ctrl shift KP_DOWN", "selectNextExtendSelection", "ctrl DOWN", "selectNextChangeLead", "ctrl KP_DOWN", "selectNextChangeLead", "RIGHT", "selectChild", "KP_RIGHT", "selectChild", "LEFT", "selectParent", "KP_LEFT", "selectParent", "PAGE_UP", "scrollUpChangeSelection", "shift PAGE_UP", "scrollUpExtendSelection", "ctrl shift PAGE_UP", "scrollUpExtendSelection", "ctrl PAGE_UP", "scrollUpChangeLead", "PAGE_DOWN", "scrollDownChangeSelection", "shift PAGE_DOWN", "scrollDownExtendSelection", "ctrl shift PAGE_DOWN", "scrollDownExtendSelection", "ctrl PAGE_DOWN", "scrollDownChangeLead", "HOME", "selectFirst", "shift HOME", "selectFirstExtendSelection", "ctrl shift HOME", "selectFirstExtendSelection", "ctrl HOME", "selectFirstChangeLead", "END", "selectLast", "shift END", "selectLastExtendSelection", "ctrl shift END", "selectLastExtendSelection", "ctrl END", "selectLastChangeLead", "F2", "startEditing", "ctrl A", "selectAll", "ctrl SLASH", "selectAll", "ctrl BACK_SLASH", "clearSelection", "ctrl LEFT", "scrollLeft", "ctrl KP_LEFT", "scrollLeft", "ctrl RIGHT", "scrollRight", "ctrl KP_RIGHT", "scrollRight", "SPACE", "addToSelection", "ctrl SPACE", "toggleAndAnchor", "shift SPACE", "extendTo", "ctrl shift SPACE", "moveSelectionTo"}), "Tree.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"ESCAPE", "cancel"}), "ToolBar.border", toolBarBorder, "ToolBar.background", menuBackground, "ToolBar.foreground", getMenuForeground(), "ToolBar.font", menuTextValue, "ToolBar.dockingBackground", menuBackground, "ToolBar.floatingBackground", menuBackground, "ToolBar.dockingForeground", primaryControlDarkShadow, "ToolBar.floatingForeground", primaryControl, "ToolBar.rolloverBorder", new MetalLookAndFeel$MetalLazyValue("javax.swing.plaf.metal.MetalBorders", "getToolBarRolloverBorder"), "ToolBar.nonrolloverBorder", new MetalLookAndFeel$MetalLazyValue("javax.swing.plaf.metal.MetalBorders", "getToolBarNonrolloverBorder"), "ToolBar.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"UP", "navigateUp", "KP_UP", "navigateUp", "DOWN", "navigateDown", "KP_DOWN", "navigateDown", "LEFT", "navigateLeft", "KP_LEFT", "navigateLeft", "RIGHT", "navigateRight", "KP_RIGHT", "navigateRight"}), "RootPane.frameBorder", new MetalLookAndFeel$MetalLazyValue("javax.swing.plaf.metal.MetalBorders$FrameBorder"), "RootPane.plainDialogBorder", dialogBorder, "RootPane.informationDialogBorder", dialogBorder, "RootPane.errorDialogBorder", new MetalLookAndFeel$MetalLazyValue("javax.swing.plaf.metal.MetalBorders$ErrorDialogBorder"), "RootPane.colorChooserDialogBorder", questionDialogBorder, "RootPane.fileChooserDialogBorder", questionDialogBorder, "RootPane.questionDialogBorder", questionDialogBorder, "RootPane.warningDialogBorder", new MetalLookAndFeel$MetalLazyValue("javax.swing.plaf.metal.MetalBorders$WarningDialogBorder"), "RootPane.defaultButtonWindowKeyBindings", new Object[]{"ENTER", "press", "released ENTER", "release", "ctrl ENTER", "press", "ctrl released ENTER", "release"}};
        table.putDefaults(defaults);
        if (isWindows() && useSystemFonts() && theme.isSystemTheme()) {
            Toolkit kit = Toolkit.getDefaultToolkit();
            Object messageFont = new MetalFontDesktopProperty("win.messagebox.font.height", kit, MetalTheme.CONTROL_TEXT_FONT);
            defaults = new Object[]{"OptionPane.messageFont", messageFont, "OptionPane.buttonFont", messageFont};
            table.putDefaults(defaults);
        }
    }
    
    protected void createDefaultTheme() {
        getCurrentTheme();
    }
    
    public UIDefaults getDefaults() {
        METAL_LOOK_AND_FEEL_INITED = true;
        createDefaultTheme();
        UIDefaults table = super.getDefaults();
        currentTheme.addCustomEntriesToTable(table);
        currentTheme.install();
        return table;
    }
    
    public void provideErrorFeedback(Component component) {
        super.provideErrorFeedback(component);
    }
    
    public static void setCurrentTheme(MetalTheme theme) {
        if (theme == null) {
            throw new NullPointerException("Can\'t have null theme");
        }
        currentTheme = theme;
        cachedAppContext = AppContext.getAppContext();
        cachedAppContext.put("currentMetalTheme", theme);
    }
    
    public static MetalTheme getCurrentTheme() {
        AppContext context = AppContext.getAppContext();
        if (cachedAppContext != context) {
            currentTheme = (MetalTheme)(MetalTheme)context.get("currentMetalTheme");
            if (currentTheme == null) {
                if (useHighContrastTheme()) {
                    currentTheme = new MetalHighContrastTheme();
                } else {
                    String theme = (String)(String)AccessController.doPrivileged(new GetPropertyAction("swing.metalTheme"));
                    if ("steel".equals(theme)) {
                        currentTheme = new DefaultMetalTheme();
                    } else {
                        currentTheme = new OceanTheme();
                    }
                }
                setCurrentTheme(currentTheme);
            }
            cachedAppContext = context;
        }
        return currentTheme;
    }
    
    public Icon getDisabledIcon(JComponent component, Icon icon) {
        if ((icon instanceof ImageIcon) && MetalLookAndFeel.usingOcean()) {
            return MetalUtils.getOceanDisabledButtonIcon(((ImageIcon)(ImageIcon)icon).getImage());
        }
        return super.getDisabledIcon(component, icon);
    }
    
    public Icon getDisabledSelectedIcon(JComponent component, Icon icon) {
        if ((icon instanceof ImageIcon) && MetalLookAndFeel.usingOcean()) {
            return MetalUtils.getOceanDisabledButtonIcon(((ImageIcon)(ImageIcon)icon).getImage());
        }
        return super.getDisabledSelectedIcon(component, icon);
    }
    
    public static FontUIResource getControlTextFont() {
        return getCurrentTheme().getControlTextFont();
    }
    
    public static FontUIResource getSystemTextFont() {
        return getCurrentTheme().getSystemTextFont();
    }
    
    public static FontUIResource getUserTextFont() {
        return getCurrentTheme().getUserTextFont();
    }
    
    public static FontUIResource getMenuTextFont() {
        return getCurrentTheme().getMenuTextFont();
    }
    
    public static FontUIResource getWindowTitleFont() {
        return getCurrentTheme().getWindowTitleFont();
    }
    
    public static FontUIResource getSubTextFont() {
        return getCurrentTheme().getSubTextFont();
    }
    
    public static ColorUIResource getDesktopColor() {
        return getCurrentTheme().getDesktopColor();
    }
    
    public static ColorUIResource getFocusColor() {
        return getCurrentTheme().getFocusColor();
    }
    
    public static ColorUIResource getWhite() {
        return getCurrentTheme().getWhite();
    }
    
    public static ColorUIResource getBlack() {
        return getCurrentTheme().getBlack();
    }
    
    public static ColorUIResource getControl() {
        return getCurrentTheme().getControl();
    }
    
    public static ColorUIResource getControlShadow() {
        return getCurrentTheme().getControlShadow();
    }
    
    public static ColorUIResource getControlDarkShadow() {
        return getCurrentTheme().getControlDarkShadow();
    }
    
    public static ColorUIResource getControlInfo() {
        return getCurrentTheme().getControlInfo();
    }
    
    public static ColorUIResource getControlHighlight() {
        return getCurrentTheme().getControlHighlight();
    }
    
    public static ColorUIResource getControlDisabled() {
        return getCurrentTheme().getControlDisabled();
    }
    
    public static ColorUIResource getPrimaryControl() {
        return getCurrentTheme().getPrimaryControl();
    }
    
    public static ColorUIResource getPrimaryControlShadow() {
        return getCurrentTheme().getPrimaryControlShadow();
    }
    
    public static ColorUIResource getPrimaryControlDarkShadow() {
        return getCurrentTheme().getPrimaryControlDarkShadow();
    }
    
    public static ColorUIResource getPrimaryControlInfo() {
        return getCurrentTheme().getPrimaryControlInfo();
    }
    
    public static ColorUIResource getPrimaryControlHighlight() {
        return getCurrentTheme().getPrimaryControlHighlight();
    }
    
    public static ColorUIResource getSystemTextColor() {
        return getCurrentTheme().getSystemTextColor();
    }
    
    public static ColorUIResource getControlTextColor() {
        return getCurrentTheme().getControlTextColor();
    }
    
    public static ColorUIResource getInactiveControlTextColor() {
        return getCurrentTheme().getInactiveControlTextColor();
    }
    
    public static ColorUIResource getInactiveSystemTextColor() {
        return getCurrentTheme().getInactiveSystemTextColor();
    }
    
    public static ColorUIResource getUserTextColor() {
        return getCurrentTheme().getUserTextColor();
    }
    
    public static ColorUIResource getTextHighlightColor() {
        return getCurrentTheme().getTextHighlightColor();
    }
    
    public static ColorUIResource getHighlightedTextColor() {
        return getCurrentTheme().getHighlightedTextColor();
    }
    
    public static ColorUIResource getWindowBackground() {
        return getCurrentTheme().getWindowBackground();
    }
    
    public static ColorUIResource getWindowTitleBackground() {
        return getCurrentTheme().getWindowTitleBackground();
    }
    
    public static ColorUIResource getWindowTitleForeground() {
        return getCurrentTheme().getWindowTitleForeground();
    }
    
    public static ColorUIResource getWindowTitleInactiveBackground() {
        return getCurrentTheme().getWindowTitleInactiveBackground();
    }
    
    public static ColorUIResource getWindowTitleInactiveForeground() {
        return getCurrentTheme().getWindowTitleInactiveForeground();
    }
    
    public static ColorUIResource getMenuBackground() {
        return getCurrentTheme().getMenuBackground();
    }
    
    public static ColorUIResource getMenuForeground() {
        return getCurrentTheme().getMenuForeground();
    }
    
    public static ColorUIResource getMenuSelectedBackground() {
        return getCurrentTheme().getMenuSelectedBackground();
    }
    
    public static ColorUIResource getMenuSelectedForeground() {
        return getCurrentTheme().getMenuSelectedForeground();
    }
    
    public static ColorUIResource getMenuDisabledForeground() {
        return getCurrentTheme().getMenuDisabledForeground();
    }
    
    public static ColorUIResource getSeparatorBackground() {
        return getCurrentTheme().getSeparatorBackground();
    }
    
    public static ColorUIResource getSeparatorForeground() {
        return getCurrentTheme().getSeparatorForeground();
    }
    
    public static ColorUIResource getAcceleratorForeground() {
        return getCurrentTheme().getAcceleratorForeground();
    }
    
    public static ColorUIResource getAcceleratorSelectedForeground() {
        return getCurrentTheme().getAcceleratorSelectedForeground();
    }
    {
    }
    {
    }
}
