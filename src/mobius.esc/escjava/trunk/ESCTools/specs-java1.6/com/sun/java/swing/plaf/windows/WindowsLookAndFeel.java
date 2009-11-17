package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import javax.swing.text.DefaultEditorKit;
import java.awt.Font;
import java.awt.Color;
import java.awt.event.KeyEvent;
import java.security.AccessController;
import java.util.*;
import sun.security.action.GetPropertyAction;
import sun.swing.SwingLazyValue;
import com.sun.java.swing.SwingUtilities2;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.WindowsIconFactory.VistaMenuItemCheckIconFactory;

public class WindowsLookAndFeel extends BasicLookAndFeel {
    
    /*synthetic*/ static Toolkit access$000(WindowsLookAndFeel x0) {
        return x0.toolkit;
    }
    
    public WindowsLookAndFeel() {
        
    }
    private Toolkit toolkit;
    private boolean updatePending = false;
    private boolean useSystemFontSettings = true;
    private boolean useSystemFontSizeSettings;
    private DesktopProperty themeActive;
    private DesktopProperty dllName;
    private DesktopProperty colorName;
    private DesktopProperty sizeName;
    
    public String getName() {
        return "Windows";
    }
    
    public String getDescription() {
        return "The Microsoft Windows Look and Feel";
    }
    
    public String getID() {
        return "Windows";
    }
    
    public boolean isNativeLookAndFeel() {
        String osName = System.getProperty("os.name");
        return (osName != null) && (osName.indexOf("Windows") != -1);
    }
    
    public boolean isSupportedLookAndFeel() {
        return isNativeLookAndFeel();
    }
    
    public void initialize() {
        super.initialize();
        toolkit = Toolkit.getDefaultToolkit();
        String osVersion = System.getProperty("os.version");
        if (osVersion != null) {
            Float version = Float.valueOf(osVersion);
            if (version.floatValue() <= 4.0) {
                isClassicWindows = true;
            } else {
                isClassicWindows = false;
                XPStyle.invalidateStyle();
            }
        }
        String systemFonts = (String)(String)java.security.AccessController.doPrivileged(new GetPropertyAction("swing.useSystemFontSettings"));
        useSystemFontSettings = (systemFonts == null || Boolean.valueOf(systemFonts).booleanValue());
        if (useSystemFontSettings) {
            Object value = UIManager.get("Application.useSystemFontSettings");
            useSystemFontSettings = (value == null || Boolean.TRUE.equals(value));
        }
        KeyboardFocusManager.getCurrentKeyboardFocusManager().addKeyEventPostProcessor(WindowsRootPaneUI.altProcessor);
    }
    
    protected void initClassDefaults(UIDefaults table) {
        super.initClassDefaults(table);
        final String windowsPackageName = "com.sun.java.swing.plaf.windows.";
        Object[] uiDefaults = {"ButtonUI", windowsPackageName + "WindowsButtonUI", "CheckBoxUI", windowsPackageName + "WindowsCheckBoxUI", "CheckBoxMenuItemUI", windowsPackageName + "WindowsCheckBoxMenuItemUI", "LabelUI", windowsPackageName + "WindowsLabelUI", "RadioButtonUI", windowsPackageName + "WindowsRadioButtonUI", "RadioButtonMenuItemUI", windowsPackageName + "WindowsRadioButtonMenuItemUI", "ToggleButtonUI", windowsPackageName + "WindowsToggleButtonUI", "ProgressBarUI", windowsPackageName + "WindowsProgressBarUI", "SliderUI", windowsPackageName + "WindowsSliderUI", "SeparatorUI", windowsPackageName + "WindowsSeparatorUI", "SplitPaneUI", windowsPackageName + "WindowsSplitPaneUI", "SpinnerUI", windowsPackageName + "WindowsSpinnerUI", "TabbedPaneUI", windowsPackageName + "WindowsTabbedPaneUI", "TextAreaUI", windowsPackageName + "WindowsTextAreaUI", "TextFieldUI", windowsPackageName + "WindowsTextFieldUI", "PasswordFieldUI", windowsPackageName + "WindowsPasswordFieldUI", "TextPaneUI", windowsPackageName + "WindowsTextPaneUI", "EditorPaneUI", windowsPackageName + "WindowsEditorPaneUI", "TreeUI", windowsPackageName + "WindowsTreeUI", "ToolBarUI", windowsPackageName + "WindowsToolBarUI", "ToolBarSeparatorUI", windowsPackageName + "WindowsToolBarSeparatorUI", "ComboBoxUI", windowsPackageName + "WindowsComboBoxUI", "TableHeaderUI", windowsPackageName + "WindowsTableHeaderUI", "InternalFrameUI", windowsPackageName + "WindowsInternalFrameUI", "DesktopPaneUI", windowsPackageName + "WindowsDesktopPaneUI", "DesktopIconUI", windowsPackageName + "WindowsDesktopIconUI", "FileChooserUI", windowsPackageName + "WindowsFileChooserUI", "MenuUI", windowsPackageName + "WindowsMenuUI", "MenuItemUI", windowsPackageName + "WindowsMenuItemUI", "MenuBarUI", windowsPackageName + "WindowsMenuBarUI", "PopupMenuUI", windowsPackageName + "WindowsPopupMenuUI", "PopupMenuSeparatorUI", windowsPackageName + "WindowsPopupMenuSeparatorUI", "ScrollBarUI", windowsPackageName + "WindowsScrollBarUI", "RootPaneUI", windowsPackageName + "WindowsRootPaneUI"};
        table.putDefaults(uiDefaults);
    }
    
    protected void initSystemColorDefaults(UIDefaults table) {
        String[] defaultSystemColors = {"desktop", "#005C5C", "activeCaption", "#000080", "activeCaptionText", "#FFFFFF", "activeCaptionBorder", "#C0C0C0", "inactiveCaption", "#808080", "inactiveCaptionText", "#C0C0C0", "inactiveCaptionBorder", "#C0C0C0", "window", "#FFFFFF", "windowBorder", "#000000", "windowText", "#000000", "menu", "#C0C0C0", "menuPressedItemB", "#000080", "menuPressedItemF", "#FFFFFF", "menuText", "#000000", "text", "#C0C0C0", "textText", "#000000", "textHighlight", "#000080", "textHighlightText", "#FFFFFF", "textInactiveText", "#808080", "control", "#C0C0C0", "controlText", "#000000", "controlHighlight", "#C0C0C0", "controlLtHighlight", "#FFFFFF", "controlShadow", "#808080", "controlDkShadow", "#000000", "scrollbar", "#E0E0E0", "info", "#FFFFE1", "infoText", "#000000"};
        loadSystemColors(table, defaultSystemColors, isNativeLookAndFeel());
    }
    
    private void initResourceBundle(UIDefaults table) {
        table.addResourceBundle("com.sun.java.swing.plaf.windows.resources.windows");
    }
    
    protected void initComponentDefaults(UIDefaults table) {
        super.initComponentDefaults(table);
        initResourceBundle(table);
        Integer twelve = new Integer(12);
        Integer eight = new Integer(8);
        Integer ten = new Integer(10);
        Integer fontPlain = new Integer(Font.PLAIN);
        Integer fontBold = new Integer(Font.BOLD);
        Object dialogPlain12 = new SwingLazyValue("javax.swing.plaf.FontUIResource", null, new Object[]{"Dialog", fontPlain, twelve});
        Object sansSerifPlain12 = new SwingLazyValue("javax.swing.plaf.FontUIResource", null, new Object[]{"SansSerif", fontPlain, twelve});
        Object monospacedPlain12 = new SwingLazyValue("javax.swing.plaf.FontUIResource", null, new Object[]{"MonoSpaced", fontPlain, twelve});
        Object dialogBold12 = new SwingLazyValue("javax.swing.plaf.FontUIResource", null, new Object[]{"Dialog", fontBold, twelve});
        ColorUIResource red = new ColorUIResource(Color.red);
        ColorUIResource black = new ColorUIResource(Color.black);
        ColorUIResource white = new ColorUIResource(Color.white);
        ColorUIResource yellow = new ColorUIResource(Color.yellow);
        ColorUIResource gray = new ColorUIResource(Color.gray);
        ColorUIResource lightGray = new ColorUIResource(Color.lightGray);
        ColorUIResource darkGray = new ColorUIResource(Color.darkGray);
        ColorUIResource scrollBarTrack = lightGray;
        ColorUIResource scrollBarTrackHighlight = darkGray;
        String osVersion = System.getProperty("os.version");
        if (osVersion != null) {
            try {
                Float version = Float.valueOf(osVersion);
                if (version.floatValue() <= 4.0) {
                    isClassicWindows = true;
                } else {
                    isClassicWindows = false;
                }
            } catch (NumberFormatException ex) {
                isClassicWindows = false;
            }
        }
        ColorUIResource treeSelection = new ColorUIResource(0, 0, 128);
        Object treeExpandedIcon = WindowsTreeUI$ExpandedIcon.createExpandedIcon();
        Object treeCollapsedIcon = WindowsTreeUI$CollapsedIcon.createCollapsedIcon();
        Object fieldInputMap = new UIDefaults$LazyInputMap(new Object[]{"control C", DefaultEditorKit.copyAction, "control V", DefaultEditorKit.pasteAction, "control X", DefaultEditorKit.cutAction, "COPY", DefaultEditorKit.copyAction, "PASTE", DefaultEditorKit.pasteAction, "CUT", DefaultEditorKit.cutAction, "control INSERT", DefaultEditorKit.copyAction, "shift INSERT", DefaultEditorKit.pasteAction, "shift DELETE", DefaultEditorKit.cutAction, "control A", DefaultEditorKit.selectAllAction, "control BACK_SLASH", "unselect", "shift LEFT", DefaultEditorKit.selectionBackwardAction, "shift RIGHT", DefaultEditorKit.selectionForwardAction, "control LEFT", DefaultEditorKit.previousWordAction, "control RIGHT", DefaultEditorKit.nextWordAction, "control shift LEFT", DefaultEditorKit.selectionPreviousWordAction, "control shift RIGHT", DefaultEditorKit.selectionNextWordAction, "HOME", DefaultEditorKit.beginLineAction, "END", DefaultEditorKit.endLineAction, "shift HOME", DefaultEditorKit.selectionBeginLineAction, "shift END", DefaultEditorKit.selectionEndLineAction, "BACK_SPACE", DefaultEditorKit.deletePrevCharAction, "ctrl H", DefaultEditorKit.deletePrevCharAction, "DELETE", DefaultEditorKit.deleteNextCharAction, "RIGHT", DefaultEditorKit.forwardAction, "LEFT", DefaultEditorKit.backwardAction, "KP_RIGHT", DefaultEditorKit.forwardAction, "KP_LEFT", DefaultEditorKit.backwardAction, "ENTER", JTextField.notifyAction, "control shift O", "toggle-componentOrientation"});
        Object passwordInputMap = new UIDefaults$LazyInputMap(new Object[]{"control C", DefaultEditorKit.copyAction, "control V", DefaultEditorKit.pasteAction, "control X", DefaultEditorKit.cutAction, "COPY", DefaultEditorKit.copyAction, "PASTE", DefaultEditorKit.pasteAction, "CUT", DefaultEditorKit.cutAction, "control INSERT", DefaultEditorKit.copyAction, "shift INSERT", DefaultEditorKit.pasteAction, "shift DELETE", DefaultEditorKit.cutAction, "control A", DefaultEditorKit.selectAllAction, "control BACK_SLASH", "unselect", "shift LEFT", DefaultEditorKit.selectionBackwardAction, "shift RIGHT", DefaultEditorKit.selectionForwardAction, "control LEFT", DefaultEditorKit.beginLineAction, "control RIGHT", DefaultEditorKit.endLineAction, "control shift LEFT", DefaultEditorKit.selectionBeginLineAction, "control shift RIGHT", DefaultEditorKit.selectionEndLineAction, "HOME", DefaultEditorKit.beginLineAction, "END", DefaultEditorKit.endLineAction, "shift HOME", DefaultEditorKit.selectionBeginLineAction, "shift END", DefaultEditorKit.selectionEndLineAction, "BACK_SPACE", DefaultEditorKit.deletePrevCharAction, "ctrl H", DefaultEditorKit.deletePrevCharAction, "DELETE", DefaultEditorKit.deleteNextCharAction, "RIGHT", DefaultEditorKit.forwardAction, "LEFT", DefaultEditorKit.backwardAction, "KP_RIGHT", DefaultEditorKit.forwardAction, "KP_LEFT", DefaultEditorKit.backwardAction, "ENTER", JTextField.notifyAction, "control shift O", "toggle-componentOrientation"});
        Object multilineInputMap = new UIDefaults$LazyInputMap(new Object[]{"control C", DefaultEditorKit.copyAction, "control V", DefaultEditorKit.pasteAction, "control X", DefaultEditorKit.cutAction, "COPY", DefaultEditorKit.copyAction, "PASTE", DefaultEditorKit.pasteAction, "CUT", DefaultEditorKit.cutAction, "control INSERT", DefaultEditorKit.copyAction, "shift INSERT", DefaultEditorKit.pasteAction, "shift DELETE", DefaultEditorKit.cutAction, "shift LEFT", DefaultEditorKit.selectionBackwardAction, "shift RIGHT", DefaultEditorKit.selectionForwardAction, "control LEFT", DefaultEditorKit.previousWordAction, "control RIGHT", DefaultEditorKit.nextWordAction, "control shift LEFT", DefaultEditorKit.selectionPreviousWordAction, "control shift RIGHT", DefaultEditorKit.selectionNextWordAction, "control A", DefaultEditorKit.selectAllAction, "control BACK_SLASH", "unselect", "HOME", DefaultEditorKit.beginLineAction, "END", DefaultEditorKit.endLineAction, "shift HOME", DefaultEditorKit.selectionBeginLineAction, "shift END", DefaultEditorKit.selectionEndLineAction, "control HOME", DefaultEditorKit.beginAction, "control END", DefaultEditorKit.endAction, "control shift HOME", DefaultEditorKit.selectionBeginAction, "control shift END", DefaultEditorKit.selectionEndAction, "UP", DefaultEditorKit.upAction, "DOWN", DefaultEditorKit.downAction, "BACK_SPACE", DefaultEditorKit.deletePrevCharAction, "ctrl H", DefaultEditorKit.deletePrevCharAction, "DELETE", DefaultEditorKit.deleteNextCharAction, "RIGHT", DefaultEditorKit.forwardAction, "LEFT", DefaultEditorKit.backwardAction, "KP_RIGHT", DefaultEditorKit.forwardAction, "KP_LEFT", DefaultEditorKit.backwardAction, "PAGE_UP", DefaultEditorKit.pageUpAction, "PAGE_DOWN", DefaultEditorKit.pageDownAction, "shift PAGE_UP", "selection-page-up", "shift PAGE_DOWN", "selection-page-down", "ctrl shift PAGE_UP", "selection-page-left", "ctrl shift PAGE_DOWN", "selection-page-right", "shift UP", DefaultEditorKit.selectionUpAction, "shift DOWN", DefaultEditorKit.selectionDownAction, "ENTER", DefaultEditorKit.insertBreakAction, "TAB", DefaultEditorKit.insertTabAction, "control T", "next-link-action", "control shift T", "previous-link-action", "control SPACE", "activate-link-action", "control shift O", "toggle-componentOrientation"});
        Object menuItemAcceleratorDelimiter = new String("+");
        Object ControlBackgroundColor = new DesktopProperty("win.3d.backgroundColor", table.get("control"), toolkit);
        Object ControlLightColor = new DesktopProperty("win.3d.lightColor", table.get("controlHighlight"), toolkit);
        Object ControlHighlightColor = new DesktopProperty("win.3d.highlightColor", table.get("controlLtHighlight"), toolkit);
        Object ControlShadowColor = new DesktopProperty("win.3d.shadowColor", table.get("controlShadow"), toolkit);
        Object ControlDarkShadowColor = new DesktopProperty("win.3d.darkShadowColor", table.get("controlDkShadow"), toolkit);
        Object ControlTextColor = new DesktopProperty("win.button.textColor", table.get("controlText"), toolkit);
        Object MenuBackgroundColor = new DesktopProperty("win.menu.backgroundColor", table.get("menu"), toolkit);
        Object MenuBarBackgroundColor = new DesktopProperty("win.menubar.backgroundColor", table.get("menu"), toolkit);
        Object MenuTextColor = new DesktopProperty("win.menu.textColor", table.get("menuText"), toolkit);
        Object SelectionBackgroundColor = new DesktopProperty("win.item.highlightColor", table.get("textHighlight"), toolkit);
        Object SelectionTextColor = new DesktopProperty("win.item.highlightTextColor", table.get("textHighlightText"), toolkit);
        Object WindowBackgroundColor = new DesktopProperty("win.frame.backgroundColor", table.get("window"), toolkit);
        Object WindowTextColor = new DesktopProperty("win.frame.textColor", table.get("windowText"), toolkit);
        Object WindowBorderWidth = new DesktopProperty("win.frame.sizingBorderWidth", new Integer(1), toolkit);
        Object TitlePaneHeight = new DesktopProperty("win.frame.captionHeight", new Integer(18), toolkit);
        Object TitleButtonWidth = new DesktopProperty("win.frame.captionButtonWidth", new Integer(16), toolkit);
        Object TitleButtonHeight = new DesktopProperty("win.frame.captionButtonHeight", new Integer(16), toolkit);
        Object InactiveTextColor = new DesktopProperty("win.text.grayedTextColor", table.get("textInactiveText"), toolkit);
        Object ScrollbarBackgroundColor = new DesktopProperty("win.scrollbar.backgroundColor", table.get("scrollbar"), toolkit);
        Object TextBackground = new WindowsLookAndFeel$XPColorValue(TMSchema$Part.EP_EDIT, null, TMSchema$Prop.FILLCOLOR, WindowBackgroundColor);
        Object ReadOnlyTextBackground = new WindowsLookAndFeel$XPColorValue(TMSchema$Part.EP_EDITTEXT, TMSchema$State.READONLY, TMSchema$Prop.FILLCOLOR, ControlBackgroundColor);
        Object DisabledTextBackground = new WindowsLookAndFeel$XPColorValue(TMSchema$Part.EP_EDITTEXT, TMSchema$State.DISABLED, TMSchema$Prop.FILLCOLOR, ControlBackgroundColor);
        Object MenuFont = dialogPlain12;
        Object FixedControlFont = monospacedPlain12;
        Object ControlFont = dialogPlain12;
        Object MessageFont = dialogPlain12;
        Object WindowFont = dialogBold12;
        Object ToolTipFont = sansSerifPlain12;
        Object IconFont = ControlFont;
        Object scrollBarWidth = new DesktopProperty("win.scrollbar.width", new Integer(16), toolkit);
        Object showMnemonics = new DesktopProperty("win.menu.keyboardCuesOn", Boolean.TRUE, toolkit);
        if (useSystemFontSettings) {
            MenuFont = getDesktopFontValue("win.menu.font", MenuFont, toolkit);
            FixedControlFont = getDesktopFontValue("win.ansiFixed.font", FixedControlFont, toolkit);
            ControlFont = getDesktopFontValue("win.defaultGUI.font", ControlFont, toolkit);
            MessageFont = getDesktopFontValue("win.messagebox.font", MessageFont, toolkit);
            WindowFont = getDesktopFontValue("win.frame.captionFont", WindowFont, toolkit);
            IconFont = getDesktopFontValue("win.icon.font", IconFont, toolkit);
            ToolTipFont = getDesktopFontValue("win.tooltip.font", ToolTipFont, toolkit);
        }
        if (useSystemFontSizeSettings) {
            MenuFont = new WindowsLookAndFeel$WindowsFontSizeProperty("win.menu.font.height", toolkit, "Dialog", Font.PLAIN, 12);
            FixedControlFont = new WindowsLookAndFeel$WindowsFontSizeProperty("win.ansiFixed.font.height", toolkit, "MonoSpaced", Font.PLAIN, 12);
            ControlFont = new WindowsLookAndFeel$WindowsFontSizeProperty("win.defaultGUI.font.height", toolkit, "Dialog", Font.PLAIN, 12);
            MessageFont = new WindowsLookAndFeel$WindowsFontSizeProperty("win.messagebox.font.height", toolkit, "Dialog", Font.PLAIN, 12);
            WindowFont = new WindowsLookAndFeel$WindowsFontSizeProperty("win.frame.captionFont.height", toolkit, "Dialog", Font.BOLD, 12);
            ToolTipFont = new WindowsLookAndFeel$WindowsFontSizeProperty("win.tooltip.font.height", toolkit, "SansSerif", Font.PLAIN, 12);
            IconFont = new WindowsLookAndFeel$WindowsFontSizeProperty("win.icon.font.height", toolkit, "Dialog", Font.PLAIN, 12);
        }
        if (!(this instanceof WindowsClassicLookAndFeel) && (System.getProperty("os.name").startsWith("Windows ") && System.getProperty("os.version").compareTo("5.1") >= 0) && AccessController.doPrivileged(new GetPropertyAction("swing.noxp")) == null) {
            this.themeActive = new WindowsLookAndFeel$TriggerDesktopProperty(this, "win.xpstyle.themeActive");
            this.dllName = new WindowsLookAndFeel$TriggerDesktopProperty(this, "win.xpstyle.dllName");
            this.colorName = new WindowsLookAndFeel$TriggerDesktopProperty(this, "win.xpstyle.colorName");
            this.sizeName = new WindowsLookAndFeel$TriggerDesktopProperty(this, "win.xpstyle.sizeName");
        }
        Object[] defaults = {"AuditoryCues.playList", null, "Application.useSystemFontSettings", Boolean.valueOf(useSystemFontSettings), "TextField.focusInputMap", fieldInputMap, "PasswordField.focusInputMap", passwordInputMap, "TextArea.focusInputMap", multilineInputMap, "TextPane.focusInputMap", multilineInputMap, "EditorPane.focusInputMap", multilineInputMap, "Button.font", ControlFont, "Button.background", ControlBackgroundColor, "Button.foreground", ControlTextColor, "Button.shadow", ControlShadowColor, "Button.darkShadow", ControlDarkShadowColor, "Button.light", ControlLightColor, "Button.highlight", ControlHighlightColor, "Button.disabledForeground", InactiveTextColor, "Button.disabledShadow", ControlHighlightColor, "Button.focus", black, "Button.dashedRectGapX", new Integer(5), "Button.dashedRectGapY", new Integer(4), "Button.dashedRectGapWidth", new Integer(10), "Button.dashedRectGapHeight", new Integer(8), "Button.textShiftOffset", new Integer(1), "Button.showMnemonics", showMnemonics, "Button.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"SPACE", "pressed", "released SPACE", "released"}), "CheckBox.font", ControlFont, "CheckBox.interiorBackground", WindowBackgroundColor, "CheckBox.background", ControlBackgroundColor, "CheckBox.foreground", ControlTextColor, "CheckBox.shadow", ControlShadowColor, "CheckBox.darkShadow", ControlDarkShadowColor, "CheckBox.light", ControlLightColor, "CheckBox.highlight", ControlHighlightColor, "CheckBox.focus", black, "CheckBox.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"SPACE", "pressed", "released SPACE", "released"}), "CheckBoxMenuItem.font", MenuFont, "CheckBoxMenuItem.background", MenuBackgroundColor, "CheckBoxMenuItem.foreground", MenuTextColor, "CheckBoxMenuItem.selectionForeground", SelectionTextColor, "CheckBoxMenuItem.selectionBackground", SelectionBackgroundColor, "CheckBoxMenuItem.acceleratorForeground", MenuTextColor, "CheckBoxMenuItem.acceleratorSelectionForeground", SelectionTextColor, "CheckBoxMenuItem.commandSound", "win.sound.menuCommand", "ComboBox.font", ControlFont, "ComboBox.background", WindowBackgroundColor, "ComboBox.foreground", WindowTextColor, "ComboBox.buttonBackground", ControlBackgroundColor, "ComboBox.buttonShadow", ControlShadowColor, "ComboBox.buttonDarkShadow", ControlDarkShadowColor, "ComboBox.buttonHighlight", ControlHighlightColor, "ComboBox.selectionBackground", SelectionBackgroundColor, "ComboBox.selectionForeground", SelectionTextColor, "ComboBox.disabledBackground", ControlBackgroundColor, "ComboBox.disabledForeground", InactiveTextColor, "ComboBox.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"ESCAPE", "hidePopup", "PAGE_UP", "pageUpPassThrough", "PAGE_DOWN", "pageDownPassThrough", "HOME", "homePassThrough", "END", "endPassThrough", "DOWN", "selectNext2", "KP_DOWN", "selectNext2", "UP", "selectPrevious2", "KP_UP", "selectPrevious2", "ENTER", "enterPressed", "F4", "togglePopup"}), "Desktop.background", new DesktopProperty("win.desktop.backgroundColor", table.get("desktop"), toolkit), "Desktop.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"ctrl F5", "restore", "ctrl F4", "close", "ctrl F7", "move", "ctrl F8", "resize", "RIGHT", "right", "KP_RIGHT", "right", "LEFT", "left", "KP_LEFT", "left", "UP", "up", "KP_UP", "up", "DOWN", "down", "KP_DOWN", "down", "ESCAPE", "escape", "ctrl F9", "minimize", "ctrl F10", "maximize", "ctrl F6", "selectNextFrame", "ctrl TAB", "selectNextFrame", "ctrl alt F6", "selectNextFrame", "shift ctrl alt F6", "selectPreviousFrame", "ctrl F12", "navigateNext", "shift ctrl F12", "navigatePrevious"}), "DesktopIcon.width", new Integer(160), "EditorPane.font", ControlFont, "EditorPane.background", WindowBackgroundColor, "EditorPane.foreground", WindowTextColor, "EditorPane.selectionBackground", SelectionBackgroundColor, "EditorPane.selectionForeground", SelectionTextColor, "EditorPane.caretForeground", WindowTextColor, "EditorPane.inactiveForeground", InactiveTextColor, "FileChooser.homeFolderIcon", new WindowsLookAndFeel$LazyWindowsIcon(null, "icons/HomeFolder.gif"), "FileChooser.listFont", IconFont, "FileChooser.listViewBackground", new WindowsLookAndFeel$XPColorValue(TMSchema$Part.LVP_LISTVIEW, null, TMSchema$Prop.FILLCOLOR, WindowBackgroundColor), "FileChooser.listViewBorder", new WindowsLookAndFeel$XPBorderValue(TMSchema$Part.LVP_LISTVIEW, new SwingLazyValue("javax.swing.plaf.BorderUIResource", "getLoweredBevelBorderUIResource")), "FileChooser.listViewIcon", new WindowsLookAndFeel$LazyWindowsIcon("fileChooserIcon ListView", "icons/ListView.gif"), "FileChooser.listViewWindowsStyle", Boolean.TRUE, "FileChooser.detailsViewIcon", new WindowsLookAndFeel$LazyWindowsIcon("fileChooserIcon DetailsView", "icons/DetailsView.gif"), "FileChooser.upFolderIcon", new WindowsLookAndFeel$LazyWindowsIcon("fileChooserIcon UpFolder", "icons/UpFolder.gif"), "FileChooser.newFolderIcon", new WindowsLookAndFeel$LazyWindowsIcon("fileChooserIcon NewFolder", "icons/NewFolder.gif"), "FileChooser.useSystemExtensionHiding", Boolean.TRUE, "FileChooser.lookInLabelMnemonic", new Integer(KeyEvent.VK_I), "FileChooser.fileNameLabelMnemonic", new Integer(KeyEvent.VK_N), "FileChooser.filesOfTypeLabelMnemonic", new Integer(KeyEvent.VK_T), "FileChooser.usesSingleFilePane", Boolean.TRUE, "FileChooser.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"ESCAPE", "cancelSelection", "F2", "editFileName", "F5", "refresh", "BACK_SPACE", "Go Up", "ENTER", "approveSelection"}), "FileView.directoryIcon", SwingUtilities2.makeIcon(getClass(), WindowsLookAndFeel.class, "icons/Directory.gif"), "FileView.fileIcon", SwingUtilities2.makeIcon(getClass(), WindowsLookAndFeel.class, "icons/File.gif"), "FileView.computerIcon", SwingUtilities2.makeIcon(getClass(), WindowsLookAndFeel.class, "icons/Computer.gif"), "FileView.hardDriveIcon", SwingUtilities2.makeIcon(getClass(), WindowsLookAndFeel.class, "icons/HardDrive.gif"), "FileView.floppyDriveIcon", SwingUtilities2.makeIcon(getClass(), WindowsLookAndFeel.class, "icons/FloppyDrive.gif"), "InternalFrame.titleFont", WindowFont, "InternalFrame.titlePaneHeight", TitlePaneHeight, "InternalFrame.titleButtonWidth", TitleButtonWidth, "InternalFrame.titleButtonHeight", TitleButtonHeight, "InternalFrame.borderColor", ControlBackgroundColor, "InternalFrame.borderShadow", ControlShadowColor, "InternalFrame.borderDarkShadow", ControlDarkShadowColor, "InternalFrame.borderHighlight", ControlHighlightColor, "InternalFrame.borderLight", ControlLightColor, "InternalFrame.borderWidth", WindowBorderWidth, "InternalFrame.minimizeIconBackground", ControlBackgroundColor, "InternalFrame.resizeIconHighlight", ControlLightColor, "InternalFrame.resizeIconShadow", ControlShadowColor, "InternalFrame.activeBorderColor", new DesktopProperty("win.frame.activeBorderColor", table.get("windowBorder"), toolkit), "InternalFrame.inactiveBorderColor", new DesktopProperty("win.frame.inactiveBorderColor", table.get("windowBorder"), toolkit), "InternalFrame.activeTitleBackground", new DesktopProperty("win.frame.activeCaptionColor", table.get("activeCaption"), toolkit), "InternalFrame.activeTitleGradient", new DesktopProperty("win.frame.activeCaptionGradientColor", table.get("activeCaption"), toolkit), "InternalFrame.activeTitleForeground", new DesktopProperty("win.frame.captionTextColor", table.get("activeCaptionText"), toolkit), "InternalFrame.inactiveTitleBackground", new DesktopProperty("win.frame.inactiveCaptionColor", table.get("inactiveCaption"), toolkit), "InternalFrame.inactiveTitleGradient", new DesktopProperty("win.frame.inactiveCaptionGradientColor", table.get("inactiveCaption"), toolkit), "InternalFrame.inactiveTitleForeground", new DesktopProperty("win.frame.inactiveCaptionTextColor", table.get("inactiveCaptionText"), toolkit), "InternalFrame.maximizeIcon", WindowsIconFactory.createFrameMaximizeIcon(), "InternalFrame.minimizeIcon", WindowsIconFactory.createFrameMinimizeIcon(), "InternalFrame.iconifyIcon", WindowsIconFactory.createFrameIconifyIcon(), "InternalFrame.closeIcon", WindowsIconFactory.createFrameCloseIcon(), "InternalFrame.icon", new SwingLazyValue("com.sun.java.swing.plaf.windows.WindowsInternalFrameTitlePane$ScalableIconUIResource", new Object[][]{{SwingUtilities2.makeIcon(getClass(), BasicLookAndFeel.class, "icons/JavaCup16.png"), SwingUtilities2.makeIcon(getClass(), WindowsLookAndFeel.class, "icons/JavaCup32.png")}}), "InternalFrame.closeSound", "win.sound.close", "InternalFrame.maximizeSound", "win.sound.maximize", "InternalFrame.minimizeSound", "win.sound.minimize", "InternalFrame.restoreDownSound", "win.sound.restoreDown", "InternalFrame.restoreUpSound", "win.sound.restoreUp", "InternalFrame.windowBindings", new Object[]{"shift ESCAPE", "showSystemMenu", "ctrl SPACE", "showSystemMenu", "ESCAPE", "hideSystemMenu"}, "Label.font", ControlFont, "Label.background", ControlBackgroundColor, "Label.foreground", ControlTextColor, "Label.disabledForeground", InactiveTextColor, "Label.disabledShadow", ControlHighlightColor, "List.font", ControlFont, "List.background", WindowBackgroundColor, "List.foreground", WindowTextColor, "List.selectionBackground", SelectionBackgroundColor, "List.selectionForeground", SelectionTextColor, "List.lockToPositionOnScroll", Boolean.TRUE, "List.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"ctrl C", "copy", "ctrl V", "paste", "ctrl X", "cut", "COPY", "copy", "PASTE", "paste", "CUT", "cut", "UP", "selectPreviousRow", "KP_UP", "selectPreviousRow", "shift UP", "selectPreviousRowExtendSelection", "shift KP_UP", "selectPreviousRowExtendSelection", "ctrl shift UP", "selectPreviousRowExtendSelection", "ctrl shift KP_UP", "selectPreviousRowExtendSelection", "ctrl UP", "selectPreviousRowChangeLead", "ctrl KP_UP", "selectPreviousRowChangeLead", "DOWN", "selectNextRow", "KP_DOWN", "selectNextRow", "shift DOWN", "selectNextRowExtendSelection", "shift KP_DOWN", "selectNextRowExtendSelection", "ctrl shift DOWN", "selectNextRowExtendSelection", "ctrl shift KP_DOWN", "selectNextRowExtendSelection", "ctrl DOWN", "selectNextRowChangeLead", "ctrl KP_DOWN", "selectNextRowChangeLead", "LEFT", "selectPreviousColumn", "KP_LEFT", "selectPreviousColumn", "shift LEFT", "selectPreviousColumnExtendSelection", "shift KP_LEFT", "selectPreviousColumnExtendSelection", "ctrl shift LEFT", "selectPreviousColumnExtendSelection", "ctrl shift KP_LEFT", "selectPreviousColumnExtendSelection", "ctrl LEFT", "selectPreviousColumnChangeLead", "ctrl KP_LEFT", "selectPreviousColumnChangeLead", "RIGHT", "selectNextColumn", "KP_RIGHT", "selectNextColumn", "shift RIGHT", "selectNextColumnExtendSelection", "shift KP_RIGHT", "selectNextColumnExtendSelection", "ctrl shift RIGHT", "selectNextColumnExtendSelection", "ctrl shift KP_RIGHT", "selectNextColumnExtendSelection", "ctrl RIGHT", "selectNextColumnChangeLead", "ctrl KP_RIGHT", "selectNextColumnChangeLead", "HOME", "selectFirstRow", "shift HOME", "selectFirstRowExtendSelection", "ctrl shift HOME", "selectFirstRowExtendSelection", "ctrl HOME", "selectFirstRowChangeLead", "END", "selectLastRow", "shift END", "selectLastRowExtendSelection", "ctrl shift END", "selectLastRowExtendSelection", "ctrl END", "selectLastRowChangeLead", "PAGE_UP", "scrollUp", "shift PAGE_UP", "scrollUpExtendSelection", "ctrl shift PAGE_UP", "scrollUpExtendSelection", "ctrl PAGE_UP", "scrollUpChangeLead", "PAGE_DOWN", "scrollDown", "shift PAGE_DOWN", "scrollDownExtendSelection", "ctrl shift PAGE_DOWN", "scrollDownExtendSelection", "ctrl PAGE_DOWN", "scrollDownChangeLead", "ctrl A", "selectAll", "ctrl SLASH", "selectAll", "ctrl BACK_SLASH", "clearSelection", "SPACE", "addToSelection", "ctrl SPACE", "toggleAndAnchor", "shift SPACE", "extendTo", "ctrl shift SPACE", "moveSelectionTo"}), "PopupMenu.font", MenuFont, "PopupMenu.background", MenuBackgroundColor, "PopupMenu.foreground", MenuTextColor, "PopupMenu.popupSound", "win.sound.menuPopup", "Menu.font", MenuFont, "Menu.foreground", MenuTextColor, "Menu.background", MenuBackgroundColor, "Menu.useMenuBarBackgroundForTopLevel", Boolean.TRUE, "Menu.selectionForeground", SelectionTextColor, "Menu.selectionBackground", SelectionBackgroundColor, "Menu.acceleratorForeground", MenuTextColor, "Menu.acceleratorSelectionForeground", SelectionTextColor, "Menu.menuPopupOffsetX", new Integer(0), "Menu.menuPopupOffsetY", new Integer(0), "Menu.submenuPopupOffsetX", new Integer(-4), "Menu.submenuPopupOffsetY", new Integer(-3), "Menu.crossMenuMnemonic", Boolean.FALSE, "MenuBar.font", MenuFont, "MenuBar.background", new WindowsLookAndFeel$XPValue(MenuBarBackgroundColor, MenuBackgroundColor), "MenuBar.foreground", MenuTextColor, "MenuBar.shadow", ControlShadowColor, "MenuBar.highlight", ControlHighlightColor, "MenuBar.windowBindings", new Object[]{"F10", "takeFocus"}, "MenuItem.font", MenuFont, "MenuItem.acceleratorFont", MenuFont, "MenuItem.foreground", MenuTextColor, "MenuItem.background", MenuBackgroundColor, "MenuItem.selectionForeground", SelectionTextColor, "MenuItem.selectionBackground", SelectionBackgroundColor, "MenuItem.disabledForeground", InactiveTextColor, "MenuItem.acceleratorForeground", MenuTextColor, "MenuItem.acceleratorSelectionForeground", SelectionTextColor, "MenuItem.acceleratorDelimiter", menuItemAcceleratorDelimiter, "MenuItem.commandSound", "win.sound.menuCommand", "RadioButton.font", ControlFont, "RadioButton.interiorBackground", WindowBackgroundColor, "RadioButton.background", ControlBackgroundColor, "RadioButton.foreground", ControlTextColor, "RadioButton.shadow", ControlShadowColor, "RadioButton.darkShadow", ControlDarkShadowColor, "RadioButton.light", ControlLightColor, "RadioButton.highlight", ControlHighlightColor, "RadioButton.focus", black, "RadioButton.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"SPACE", "pressed", "released SPACE", "released"}), "RadioButtonMenuItem.font", MenuFont, "RadioButtonMenuItem.foreground", MenuTextColor, "RadioButtonMenuItem.background", MenuBackgroundColor, "RadioButtonMenuItem.selectionForeground", SelectionTextColor, "RadioButtonMenuItem.selectionBackground", SelectionBackgroundColor, "RadioButtonMenuItem.disabledForeground", InactiveTextColor, "RadioButtonMenuItem.acceleratorForeground", MenuTextColor, "RadioButtonMenuItem.acceleratorSelectionForeground", SelectionTextColor, "RadioButtonMenuItem.commandSound", "win.sound.menuCommand", "OptionPane.font", MessageFont, "OptionPane.messageFont", MessageFont, "OptionPane.buttonFont", MessageFont, "OptionPane.background", ControlBackgroundColor, "OptionPane.foreground", ControlTextColor, "OptionPane.messageForeground", ControlTextColor, "OptionPane.errorIcon", new WindowsLookAndFeel$LazyWindowsIcon("optionPaneIcon Error", "icons/Error.gif"), "OptionPane.informationIcon", new WindowsLookAndFeel$LazyWindowsIcon("optionPaneIcon Information", "icons/Inform.gif"), "OptionPane.questionIcon", new WindowsLookAndFeel$LazyWindowsIcon("optionPaneIcon Question", "icons/Question.gif"), "OptionPane.warningIcon", new WindowsLookAndFeel$LazyWindowsIcon("optionPaneIcon Warning", "icons/Warn.gif"), "OptionPane.windowBindings", new Object[]{"ESCAPE", "close"}, "OptionPane.errorSound", "win.sound.hand", "OptionPane.informationSound", "win.sound.asterisk", "OptionPane.questionSound", "win.sound.question", "OptionPane.warningSound", "win.sound.exclamation", "FormattedTextField.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"ctrl C", DefaultEditorKit.copyAction, "ctrl V", DefaultEditorKit.pasteAction, "ctrl X", DefaultEditorKit.cutAction, "COPY", DefaultEditorKit.copyAction, "PASTE", DefaultEditorKit.pasteAction, "CUT", DefaultEditorKit.cutAction, "shift LEFT", DefaultEditorKit.selectionBackwardAction, "shift KP_LEFT", DefaultEditorKit.selectionBackwardAction, "shift RIGHT", DefaultEditorKit.selectionForwardAction, "shift KP_RIGHT", DefaultEditorKit.selectionForwardAction, "ctrl LEFT", DefaultEditorKit.previousWordAction, "ctrl KP_LEFT", DefaultEditorKit.previousWordAction, "ctrl RIGHT", DefaultEditorKit.nextWordAction, "ctrl KP_RIGHT", DefaultEditorKit.nextWordAction, "ctrl shift LEFT", DefaultEditorKit.selectionPreviousWordAction, "ctrl shift KP_LEFT", DefaultEditorKit.selectionPreviousWordAction, "ctrl shift RIGHT", DefaultEditorKit.selectionNextWordAction, "ctrl shift KP_RIGHT", DefaultEditorKit.selectionNextWordAction, "ctrl A", DefaultEditorKit.selectAllAction, "HOME", DefaultEditorKit.beginLineAction, "END", DefaultEditorKit.endLineAction, "shift HOME", DefaultEditorKit.selectionBeginLineAction, "shift END", DefaultEditorKit.selectionEndLineAction, "BACK_SPACE", DefaultEditorKit.deletePrevCharAction, "ctrl H", DefaultEditorKit.deletePrevCharAction, "DELETE", DefaultEditorKit.deleteNextCharAction, "RIGHT", DefaultEditorKit.forwardAction, "LEFT", DefaultEditorKit.backwardAction, "KP_RIGHT", DefaultEditorKit.forwardAction, "KP_LEFT", DefaultEditorKit.backwardAction, "ENTER", JTextField.notifyAction, "ctrl BACK_SLASH", "unselect", "control shift O", "toggle-componentOrientation", "ESCAPE", "reset-field-edit", "UP", "increment", "KP_UP", "increment", "DOWN", "decrement", "KP_DOWN", "decrement"}), "Panel.font", ControlFont, "Panel.background", ControlBackgroundColor, "Panel.foreground", WindowTextColor, "PasswordField.font", FixedControlFont, "PasswordField.background", TextBackground, "PasswordField.foreground", WindowTextColor, "PasswordField.inactiveForeground", InactiveTextColor, "PasswordField.inactiveBackground", ReadOnlyTextBackground, "PasswordField.disabledBackground", DisabledTextBackground, "PasswordField.selectionBackground", SelectionBackgroundColor, "PasswordField.selectionForeground", SelectionTextColor, "PasswordField.caretForeground", WindowTextColor, "ProgressBar.font", ControlFont, "ProgressBar.foreground", SelectionBackgroundColor, "ProgressBar.background", ControlBackgroundColor, "ProgressBar.shadow", ControlShadowColor, "ProgressBar.highlight", ControlHighlightColor, "ProgressBar.selectionForeground", ControlBackgroundColor, "ProgressBar.selectionBackground", SelectionBackgroundColor, "ProgressBar.cellLength", new Integer(7), "ProgressBar.cellSpacing", new Integer(2), "RootPane.defaultButtonWindowKeyBindings", new Object[]{"ENTER", "press", "released ENTER", "release", "ctrl ENTER", "press", "ctrl released ENTER", "release"}, "ScrollBar.background", ScrollbarBackgroundColor, "ScrollBar.foreground", ControlBackgroundColor, "ScrollBar.track", white, "ScrollBar.trackForeground", ScrollbarBackgroundColor, "ScrollBar.trackHighlight", black, "ScrollBar.trackHighlightForeground", scrollBarTrackHighlight, "ScrollBar.thumb", ControlBackgroundColor, "ScrollBar.thumbHighlight", ControlHighlightColor, "ScrollBar.thumbDarkShadow", ControlDarkShadowColor, "ScrollBar.thumbShadow", ControlShadowColor, "ScrollBar.width", scrollBarWidth, "ScrollBar.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"RIGHT", "positiveUnitIncrement", "KP_RIGHT", "positiveUnitIncrement", "DOWN", "positiveUnitIncrement", "KP_DOWN", "positiveUnitIncrement", "PAGE_DOWN", "positiveBlockIncrement", "ctrl PAGE_DOWN", "positiveBlockIncrement", "LEFT", "negativeUnitIncrement", "KP_LEFT", "negativeUnitIncrement", "UP", "negativeUnitIncrement", "KP_UP", "negativeUnitIncrement", "PAGE_UP", "negativeBlockIncrement", "ctrl PAGE_UP", "negativeBlockIncrement", "HOME", "minScroll", "END", "maxScroll"}), "ScrollPane.font", ControlFont, "ScrollPane.background", ControlBackgroundColor, "ScrollPane.foreground", ControlTextColor, "ScrollPane.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"RIGHT", "unitScrollRight", "KP_RIGHT", "unitScrollRight", "DOWN", "unitScrollDown", "KP_DOWN", "unitScrollDown", "LEFT", "unitScrollLeft", "KP_LEFT", "unitScrollLeft", "UP", "unitScrollUp", "KP_UP", "unitScrollUp", "PAGE_UP", "scrollUp", "PAGE_DOWN", "scrollDown", "ctrl PAGE_UP", "scrollLeft", "ctrl PAGE_DOWN", "scrollRight", "ctrl HOME", "scrollHome", "ctrl END", "scrollEnd"}), "Separator.background", ControlHighlightColor, "Separator.foreground", ControlShadowColor, "Slider.foreground", ControlBackgroundColor, "Slider.background", ControlBackgroundColor, "Slider.highlight", ControlHighlightColor, "Slider.shadow", ControlShadowColor, "Slider.focus", ControlDarkShadowColor, "Slider.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"RIGHT", "positiveUnitIncrement", "KP_RIGHT", "positiveUnitIncrement", "DOWN", "negativeUnitIncrement", "KP_DOWN", "negativeUnitIncrement", "PAGE_DOWN", "negativeBlockIncrement", "LEFT", "negativeUnitIncrement", "KP_LEFT", "negativeUnitIncrement", "UP", "positiveUnitIncrement", "KP_UP", "positiveUnitIncrement", "PAGE_UP", "positiveBlockIncrement", "HOME", "minScroll", "END", "maxScroll"}), "Spinner.font", FixedControlFont, "Spinner.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"UP", "increment", "KP_UP", "increment", "DOWN", "decrement", "KP_DOWN", "decrement"}), "SplitPane.background", ControlBackgroundColor, "SplitPane.highlight", ControlHighlightColor, "SplitPane.shadow", ControlShadowColor, "SplitPane.darkShadow", ControlDarkShadowColor, "SplitPane.dividerSize", new Integer(5), "SplitPane.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"UP", "negativeIncrement", "DOWN", "positiveIncrement", "LEFT", "negativeIncrement", "RIGHT", "positiveIncrement", "KP_UP", "negativeIncrement", "KP_DOWN", "positiveIncrement", "KP_LEFT", "negativeIncrement", "KP_RIGHT", "positiveIncrement", "HOME", "selectMin", "END", "selectMax", "F8", "startResize", "F6", "toggleFocus", "ctrl TAB", "focusOutForward", "ctrl shift TAB", "focusOutBackward"}), "TabbedPane.tabsOverlapBorder", new WindowsLookAndFeel$XPValue(Boolean.TRUE, Boolean.FALSE), "TabbedPane.tabInsets", new WindowsLookAndFeel$XPValue(new InsetsUIResource(1, 4, 1, 4), new InsetsUIResource(0, 4, 1, 4)), "TabbedPane.tabAreaInsets", new WindowsLookAndFeel$XPValue(new InsetsUIResource(3, 2, 2, 2), new InsetsUIResource(3, 2, 0, 2)), "TabbedPane.font", ControlFont, "TabbedPane.background", ControlBackgroundColor, "TabbedPane.foreground", ControlTextColor, "TabbedPane.highlight", ControlHighlightColor, "TabbedPane.light", ControlLightColor, "TabbedPane.shadow", ControlShadowColor, "TabbedPane.darkShadow", ControlDarkShadowColor, "TabbedPane.focus", ControlTextColor, "TabbedPane.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"RIGHT", "navigateRight", "KP_RIGHT", "navigateRight", "LEFT", "navigateLeft", "KP_LEFT", "navigateLeft", "UP", "navigateUp", "KP_UP", "navigateUp", "DOWN", "navigateDown", "KP_DOWN", "navigateDown", "ctrl DOWN", "requestFocusForVisibleComponent", "ctrl KP_DOWN", "requestFocusForVisibleComponent"}), "TabbedPane.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"ctrl TAB", "navigateNext", "ctrl shift TAB", "navigatePrevious", "ctrl PAGE_DOWN", "navigatePageDown", "ctrl PAGE_UP", "navigatePageUp", "ctrl UP", "requestFocus", "ctrl KP_UP", "requestFocus"}), "Table.font", ControlFont, "Table.foreground", ControlTextColor, "Table.background", WindowBackgroundColor, "Table.highlight", ControlHighlightColor, "Table.light", ControlLightColor, "Table.shadow", ControlShadowColor, "Table.darkShadow", ControlDarkShadowColor, "Table.selectionForeground", SelectionTextColor, "Table.selectionBackground", SelectionBackgroundColor, "Table.gridColor", gray, "Table.focusCellBackground", WindowBackgroundColor, "Table.focusCellForeground", ControlTextColor, "Table.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"ctrl C", "copy", "ctrl V", "paste", "ctrl X", "cut", "COPY", "copy", "PASTE", "paste", "CUT", "cut", "RIGHT", "selectNextColumn", "KP_RIGHT", "selectNextColumn", "shift RIGHT", "selectNextColumnExtendSelection", "shift KP_RIGHT", "selectNextColumnExtendSelection", "ctrl shift RIGHT", "selectNextColumnExtendSelection", "ctrl shift KP_RIGHT", "selectNextColumnExtendSelection", "ctrl RIGHT", "selectNextColumnChangeLead", "ctrl KP_RIGHT", "selectNextColumnChangeLead", "LEFT", "selectPreviousColumn", "KP_LEFT", "selectPreviousColumn", "shift LEFT", "selectPreviousColumnExtendSelection", "shift KP_LEFT", "selectPreviousColumnExtendSelection", "ctrl shift LEFT", "selectPreviousColumnExtendSelection", "ctrl shift KP_LEFT", "selectPreviousColumnExtendSelection", "ctrl LEFT", "selectPreviousColumnChangeLead", "ctrl KP_LEFT", "selectPreviousColumnChangeLead", "DOWN", "selectNextRow", "KP_DOWN", "selectNextRow", "shift DOWN", "selectNextRowExtendSelection", "shift KP_DOWN", "selectNextRowExtendSelection", "ctrl shift DOWN", "selectNextRowExtendSelection", "ctrl shift KP_DOWN", "selectNextRowExtendSelection", "ctrl DOWN", "selectNextRowChangeLead", "ctrl KP_DOWN", "selectNextRowChangeLead", "UP", "selectPreviousRow", "KP_UP", "selectPreviousRow", "shift UP", "selectPreviousRowExtendSelection", "shift KP_UP", "selectPreviousRowExtendSelection", "ctrl shift UP", "selectPreviousRowExtendSelection", "ctrl shift KP_UP", "selectPreviousRowExtendSelection", "ctrl UP", "selectPreviousRowChangeLead", "ctrl KP_UP", "selectPreviousRowChangeLead", "HOME", "selectFirstColumn", "shift HOME", "selectFirstColumnExtendSelection", "ctrl shift HOME", "selectFirstRowExtendSelection", "ctrl HOME", "selectFirstRow", "END", "selectLastColumn", "shift END", "selectLastColumnExtendSelection", "ctrl shift END", "selectLastRowExtendSelection", "ctrl END", "selectLastRow", "PAGE_UP", "scrollUpChangeSelection", "shift PAGE_UP", "scrollUpExtendSelection", "ctrl shift PAGE_UP", "scrollLeftExtendSelection", "ctrl PAGE_UP", "scrollLeftChangeSelection", "PAGE_DOWN", "scrollDownChangeSelection", "shift PAGE_DOWN", "scrollDownExtendSelection", "ctrl shift PAGE_DOWN", "scrollRightExtendSelection", "ctrl PAGE_DOWN", "scrollRightChangeSelection", "TAB", "selectNextColumnCell", "shift TAB", "selectPreviousColumnCell", "ENTER", "selectNextRowCell", "shift ENTER", "selectPreviousRowCell", "ctrl A", "selectAll", "ctrl SLASH", "selectAll", "ctrl BACK_SLASH", "clearSelection", "ESCAPE", "cancel", "F2", "startEditing", "SPACE", "addToSelection", "ctrl SPACE", "toggleAndAnchor", "shift SPACE", "extendTo", "ctrl shift SPACE", "moveSelectionTo"}), "TableHeader.font", ControlFont, "TableHeader.foreground", ControlTextColor, "TableHeader.background", ControlBackgroundColor, "TextArea.font", FixedControlFont, "TextArea.background", WindowBackgroundColor, "TextArea.foreground", WindowTextColor, "TextArea.inactiveForeground", InactiveTextColor, "TextArea.selectionBackground", SelectionBackgroundColor, "TextArea.selectionForeground", SelectionTextColor, "TextArea.caretForeground", WindowTextColor, "TextField.font", ControlFont, "TextField.background", TextBackground, "TextField.foreground", WindowTextColor, "TextField.shadow", ControlShadowColor, "TextField.darkShadow", ControlDarkShadowColor, "TextField.light", ControlLightColor, "TextField.highlight", ControlHighlightColor, "TextField.inactiveForeground", InactiveTextColor, "TextField.inactiveBackground", ReadOnlyTextBackground, "TextField.disabledBackground", DisabledTextBackground, "TextField.selectionBackground", SelectionBackgroundColor, "TextField.selectionForeground", SelectionTextColor, "TextField.caretForeground", WindowTextColor, "TextPane.font", ControlFont, "TextPane.background", WindowBackgroundColor, "TextPane.foreground", WindowTextColor, "TextPane.selectionBackground", SelectionBackgroundColor, "TextPane.selectionForeground", SelectionTextColor, "TextPane.caretForeground", WindowTextColor, "TitledBorder.font", ControlFont, "TitledBorder.titleColor", new WindowsLookAndFeel$XPColorValue(TMSchema$Part.BP_GROUPBOX, null, TMSchema$Prop.TEXTCOLOR, ControlTextColor), "ToggleButton.font", ControlFont, "ToggleButton.background", ControlBackgroundColor, "ToggleButton.foreground", ControlTextColor, "ToggleButton.shadow", ControlShadowColor, "ToggleButton.darkShadow", ControlDarkShadowColor, "ToggleButton.light", ControlLightColor, "ToggleButton.highlight", ControlHighlightColor, "ToggleButton.focus", ControlTextColor, "ToggleButton.textShiftOffset", new Integer(1), "ToggleButton.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"SPACE", "pressed", "released SPACE", "released"}), "ToolBar.font", MenuFont, "ToolBar.background", ControlBackgroundColor, "ToolBar.foreground", ControlTextColor, "ToolBar.shadow", ControlShadowColor, "ToolBar.darkShadow", ControlDarkShadowColor, "ToolBar.light", ControlLightColor, "ToolBar.highlight", ControlHighlightColor, "ToolBar.dockingBackground", ControlBackgroundColor, "ToolBar.dockingForeground", red, "ToolBar.floatingBackground", ControlBackgroundColor, "ToolBar.floatingForeground", darkGray, "ToolBar.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"UP", "navigateUp", "KP_UP", "navigateUp", "DOWN", "navigateDown", "KP_DOWN", "navigateDown", "LEFT", "navigateLeft", "KP_LEFT", "navigateLeft", "RIGHT", "navigateRight", "KP_RIGHT", "navigateRight"}), "ToolBar.separatorSize", null, "ToolTip.font", ToolTipFont, "ToolTip.background", new DesktopProperty("win.tooltip.backgroundColor", table.get("info"), toolkit), "ToolTip.foreground", new DesktopProperty("win.tooltip.textColor", table.get("infoText"), toolkit), "ToolBar.rolloverBorderProvider", new WindowsLookAndFeel$1(this), "Tree.selectionBorderColor", black, "Tree.drawDashedFocusIndicator", Boolean.TRUE, "Tree.lineTypeDashed", Boolean.TRUE, "Tree.font", ControlFont, "Tree.background", WindowBackgroundColor, "Tree.foreground", WindowTextColor, "Tree.hash", gray, "Tree.textForeground", WindowTextColor, "Tree.textBackground", WindowBackgroundColor, "Tree.selectionForeground", SelectionTextColor, "Tree.selectionBackground", SelectionBackgroundColor, "Tree.expandedIcon", treeExpandedIcon, "Tree.collapsedIcon", treeCollapsedIcon, "Tree.focusInputMap", new UIDefaults$LazyInputMap(new Object[]{"ADD", "expand", "SUBTRACT", "collapse", "ctrl C", "copy", "ctrl V", "paste", "ctrl X", "cut", "COPY", "copy", "PASTE", "paste", "CUT", "cut", "UP", "selectPrevious", "KP_UP", "selectPrevious", "shift UP", "selectPreviousExtendSelection", "shift KP_UP", "selectPreviousExtendSelection", "ctrl shift UP", "selectPreviousExtendSelection", "ctrl shift KP_UP", "selectPreviousExtendSelection", "ctrl UP", "selectPreviousChangeLead", "ctrl KP_UP", "selectPreviousChangeLead", "DOWN", "selectNext", "KP_DOWN", "selectNext", "shift DOWN", "selectNextExtendSelection", "shift KP_DOWN", "selectNextExtendSelection", "ctrl shift DOWN", "selectNextExtendSelection", "ctrl shift KP_DOWN", "selectNextExtendSelection", "ctrl DOWN", "selectNextChangeLead", "ctrl KP_DOWN", "selectNextChangeLead", "RIGHT", "selectChild", "KP_RIGHT", "selectChild", "LEFT", "selectParent", "KP_LEFT", "selectParent", "PAGE_UP", "scrollUpChangeSelection", "shift PAGE_UP", "scrollUpExtendSelection", "ctrl shift PAGE_UP", "scrollUpExtendSelection", "ctrl PAGE_UP", "scrollUpChangeLead", "PAGE_DOWN", "scrollDownChangeSelection", "shift PAGE_DOWN", "scrollDownExtendSelection", "ctrl shift PAGE_DOWN", "scrollDownExtendSelection", "ctrl PAGE_DOWN", "scrollDownChangeLead", "HOME", "selectFirst", "shift HOME", "selectFirstExtendSelection", "ctrl shift HOME", "selectFirstExtendSelection", "ctrl HOME", "selectFirstChangeLead", "END", "selectLast", "shift END", "selectLastExtendSelection", "ctrl shift END", "selectLastExtendSelection", "ctrl END", "selectLastChangeLead", "F2", "startEditing", "ctrl A", "selectAll", "ctrl SLASH", "selectAll", "ctrl BACK_SLASH", "clearSelection", "ctrl LEFT", "scrollLeft", "ctrl KP_LEFT", "scrollLeft", "ctrl RIGHT", "scrollRight", "ctrl KP_RIGHT", "scrollRight", "SPACE", "addToSelection", "ctrl SPACE", "toggleAndAnchor", "shift SPACE", "extendTo", "ctrl shift SPACE", "moveSelectionTo"}), "Tree.ancestorInputMap", new UIDefaults$LazyInputMap(new Object[]{"ESCAPE", "cancel"}), "Viewport.font", ControlFont, "Viewport.background", ControlBackgroundColor, "Viewport.foreground", WindowTextColor};
        table.putDefaults(defaults);
        table.putDefaults(getLazyValueDefaults());
        initVistaComponentDefaults(table);
    }
    
    static boolean isOnVista() {
        boolean rv = false;
        String osName = System.getProperty("os.name");
        String osVers = System.getProperty("os.version");
        if (osName != null && osName.startsWith("Windows") && osVers != null && osVers.length() > 0) {
            int p = osVers.indexOf('.');
            if (p >= 0) {
                osVers = osVers.substring(0, p);
            }
            try {
                rv = (Integer.parseInt(osVers) >= 6);
            } catch (NumberFormatException nfe) {
            }
        }
        return rv;
    }
    
    private void initVistaComponentDefaults(UIDefaults table) {
        if (!isOnVista()) {
            return;
        }
        String[] menuClasses = {"MenuItem", "Menu", "CheckBoxMenuItem", "RadioButtonMenuItem"};
        Object[] menuDefaults = new Object[menuClasses.length * 2];
        for (int i = 0, j = 0; i < menuClasses.length; i++) {
            String key = menuClasses[i] + ".opaque";
            Object oldValue = table.get(key);
            menuDefaults[j++] = key;
            menuDefaults[j++] = new WindowsLookAndFeel$XPValue(Boolean.FALSE, oldValue);
        }
        table.putDefaults(menuDefaults);
        for (int i = 0, j = 0; i < menuClasses.length; i++) {
            String key = menuClasses[i] + ".acceleratorSelectionForeground";
            Object oldValue = table.get(key);
            menuDefaults[j++] = key;
            menuDefaults[j++] = new WindowsLookAndFeel$XPValue(table.getColor(menuClasses[i] + ".acceleratorForeground"), oldValue);
        }
        table.putDefaults(menuDefaults);
        WindowsIconFactory$VistaMenuItemCheckIconFactory menuItemCheckIconFactory = WindowsIconFactory.getMenuItemCheckIconFactory();
        for (int i = 0, j = 0; i < menuClasses.length; i++) {
            String key = menuClasses[i] + ".checkIconFactory";
            Object oldValue = table.get(key);
            menuDefaults[j++] = key;
            menuDefaults[j++] = new WindowsLookAndFeel$XPValue(menuItemCheckIconFactory, oldValue);
        }
        table.putDefaults(menuDefaults);
        for (int i = 0, j = 0; i < menuClasses.length; i++) {
            String key = menuClasses[i] + ".checkIcon";
            Object oldValue = table.get(key);
            menuDefaults[j++] = key;
            menuDefaults[j++] = new WindowsLookAndFeel$XPValue(menuItemCheckIconFactory.getIcon(menuClasses[i]), oldValue);
        }
        table.putDefaults(menuDefaults);
        for (int i = 0, j = 0; i < menuClasses.length; i++) {
            String key = menuClasses[i] + ".evenHeight";
            Object oldValue = table.get(key);
            menuDefaults[j++] = key;
            menuDefaults[j++] = new WindowsLookAndFeel$XPValue(Boolean.TRUE, oldValue);
        }
        table.putDefaults(menuDefaults);
        InsetsUIResource insets = new InsetsUIResource(0, 0, 0, 0);
        for (int i = 0, j = 0; i < menuClasses.length; i++) {
            String key = menuClasses[i] + ".margin";
            Object oldValue = table.get(key);
            menuDefaults[j++] = key;
            menuDefaults[j++] = new WindowsLookAndFeel$XPValue(insets, oldValue);
        }
        table.putDefaults(menuDefaults);
        Integer checkIconOffsetInteger = Integer.valueOf(0);
        for (int i = 0, j = 0; i < menuClasses.length; i++) {
            String key = menuClasses[i] + ".checkIconOffset";
            Object oldValue = table.get(key);
            menuDefaults[j++] = key;
            menuDefaults[j++] = new WindowsLookAndFeel$XPValue(checkIconOffsetInteger, oldValue);
        }
        table.putDefaults(menuDefaults);
        Object minimumTextOffset = new WindowsLookAndFeel$2(this);
        for (int i = 0, j = 0; i < menuClasses.length; i++) {
            String key = menuClasses[i] + ".minimumTextOffset";
            Object oldValue = table.get(key);
            menuDefaults[j++] = key;
            menuDefaults[j++] = new WindowsLookAndFeel$XPValue(minimumTextOffset, oldValue);
        }
        table.putDefaults(menuDefaults);
        String POPUP_MENU_BORDER = "PopupMenu.border";
        Object popupMenuBorder = new WindowsLookAndFeel$XPBorderValue(TMSchema$Part.MENU, new SwingLazyValue("javax.swing.plaf.basic.BasicBorders", "getInternalFrameBorder"), BorderFactory.createEmptyBorder(2, 2, 2, 2));
        table.put(POPUP_MENU_BORDER, popupMenuBorder);
    }
    
    private Object getDesktopFontValue(String fontName, Object backup, Toolkit kit) {
        if (useSystemFontSettings) {
            return new WindowsLookAndFeel$WindowsFontProperty(fontName, backup, kit);
        }
        return null;
    }
    
    private Object[] getLazyValueDefaults() {
        Object buttonBorder = new WindowsLookAndFeel$XPBorderValue(TMSchema$Part.BP_PUSHBUTTON, new SwingLazyValue("javax.swing.plaf.basic.BasicBorders", "getButtonBorder"));
        Object textFieldBorder = new WindowsLookAndFeel$XPBorderValue(TMSchema$Part.EP_EDIT, new SwingLazyValue("javax.swing.plaf.basic.BasicBorders", "getTextFieldBorder"));
        Object textFieldMargin = new WindowsLookAndFeel$XPValue(new InsetsUIResource(1, 5, 2, 4), new InsetsUIResource(1, 1, 1, 1));
        Object spinnerBorder = textFieldBorder;
        Object comboBoxBorder = new WindowsLookAndFeel$XPBorderValue(TMSchema$Part.CP_COMBOBOX, textFieldBorder);
        Object focusCellHighlightBorder = new SwingLazyValue("com.sun.java.swing.plaf.windows.WindowsBorders", "getFocusCellHighlightBorder");
        Object etchedBorder = new SwingLazyValue("javax.swing.plaf.BorderUIResource", "getEtchedBorderUIResource");
        Object internalFrameBorder = new SwingLazyValue("com.sun.java.swing.plaf.windows.WindowsBorders", "getInternalFrameBorder");
        Object loweredBevelBorder = new SwingLazyValue("javax.swing.plaf.BorderUIResource", "getLoweredBevelBorderUIResource");
        Object marginBorder = new SwingLazyValue("javax.swing.plaf.basic.BasicBorders$MarginBorder");
        Object menuBarBorder = new SwingLazyValue("javax.swing.plaf.basic.BasicBorders", "getMenuBarBorder");
        Object popupMenuBorder = new WindowsLookAndFeel$XPBorderValue(TMSchema$Part.MENU, new SwingLazyValue("javax.swing.plaf.basic.BasicBorders", "getInternalFrameBorder"));
        Object progressBarBorder = new SwingLazyValue("com.sun.java.swing.plaf.windows.WindowsBorders", "getProgressBarBorder");
        Object radioButtonBorder = new SwingLazyValue("javax.swing.plaf.basic.BasicBorders", "getRadioButtonBorder");
        Object scrollPaneBorder = new WindowsLookAndFeel$XPBorderValue(TMSchema$Part.LBP_LISTBOX, textFieldBorder);
        Object tableScrollPaneBorder = new WindowsLookAndFeel$XPBorderValue(TMSchema$Part.LBP_LISTBOX, loweredBevelBorder);
        Object tableHeaderBorder = new SwingLazyValue("com.sun.java.swing.plaf.windows.WindowsBorders", "getTableHeaderBorder");
        Object toolBarBorder = new SwingLazyValue("com.sun.java.swing.plaf.windows.WindowsBorders", "getToolBarBorder");
        Object toolTipBorder = new SwingLazyValue("javax.swing.plaf.BorderUIResource", "getBlackLineBorderUIResource");
        Object checkBoxIcon = new SwingLazyValue("com.sun.java.swing.plaf.windows.WindowsIconFactory", "getCheckBoxIcon");
        Object radioButtonIcon = new SwingLazyValue("com.sun.java.swing.plaf.windows.WindowsIconFactory", "getRadioButtonIcon");
        Object menuItemCheckIcon = new SwingLazyValue("com.sun.java.swing.plaf.windows.WindowsIconFactory", "getMenuItemCheckIcon");
        Object menuItemArrowIcon = new SwingLazyValue("com.sun.java.swing.plaf.windows.WindowsIconFactory", "getMenuItemArrowIcon");
        Object menuArrowIcon = new SwingLazyValue("com.sun.java.swing.plaf.windows.WindowsIconFactory", "getMenuArrowIcon");
        Object[] lazyDefaults = {"Button.border", buttonBorder, "CheckBox.border", radioButtonBorder, "ComboBox.border", comboBoxBorder, "DesktopIcon.border", internalFrameBorder, "FormattedTextField.border", textFieldBorder, "FormattedTextField.margin", textFieldMargin, "InternalFrame.border", internalFrameBorder, "List.focusCellHighlightBorder", focusCellHighlightBorder, "Table.focusCellHighlightBorder", focusCellHighlightBorder, "Menu.border", marginBorder, "MenuBar.border", menuBarBorder, "MenuItem.border", marginBorder, "PasswordField.border", textFieldBorder, "PasswordField.margin", textFieldMargin, "PopupMenu.border", popupMenuBorder, "ProgressBar.border", progressBarBorder, "RadioButton.border", radioButtonBorder, "ScrollPane.border", scrollPaneBorder, "Spinner.border", spinnerBorder, "Table.scrollPaneBorder", tableScrollPaneBorder, "TableHeader.cellBorder", tableHeaderBorder, "TextField.border", textFieldBorder, "TextField.margin", textFieldMargin, "TitledBorder.border", new WindowsLookAndFeel$XPBorderValue(TMSchema$Part.BP_GROUPBOX, etchedBorder), "ToggleButton.border", radioButtonBorder, "ToolBar.border", toolBarBorder, "ToolTip.border", toolTipBorder, "CheckBox.icon", checkBoxIcon, "Menu.arrowIcon", menuArrowIcon, "MenuItem.checkIcon", menuItemCheckIcon, "MenuItem.arrowIcon", menuItemArrowIcon, "RadioButton.icon", radioButtonIcon, "InternalFrame.layoutTitlePaneAtOrigin", new WindowsLookAndFeel$XPValue(Boolean.TRUE, Boolean.FALSE)};
        return lazyDefaults;
    }
    
    public void uninitialize() {
        super.uninitialize();
        toolkit = null;
        if (WindowsPopupMenuUI.mnemonicListener != null) {
            MenuSelectionManager.defaultManager().removeChangeListener(WindowsPopupMenuUI.mnemonicListener);
        }
        KeyboardFocusManager.getCurrentKeyboardFocusManager().removeKeyEventPostProcessor(WindowsRootPaneUI.altProcessor);
        DesktopProperty.flushUnreferencedProperties();
    }
    private static boolean isMnemonicHidden = true;
    private static boolean isClassicWindows = false;
    
    public static void setMnemonicHidden(boolean hide) {
        if (UIManager.getBoolean("Button.showMnemonics") == true) {
            isMnemonicHidden = false;
        } else {
            isMnemonicHidden = hide;
        }
    }
    
    public static boolean isMnemonicHidden() {
        if (UIManager.getBoolean("Button.showMnemonics") == true) {
            isMnemonicHidden = false;
        }
        return isMnemonicHidden;
    }
    
    public static boolean isClassicWindows() {
        return isClassicWindows;
    }
    
    public void provideErrorFeedback(Component component) {
        super.provideErrorFeedback(component);
    }
    
    protected Action createAudioAction(Object key) {
        if (key != null) {
            String audioKey = (String)(String)key;
            String audioValue = (String)(String)UIManager.get(key);
            return new WindowsLookAndFeel$AudioAction(audioKey, audioValue);
        } else {
            return null;
        }
    }
    
    static void repaintRootPane(Component c) {
        JRootPane root = null;
        for (; c != null; c = c.getParent()) {
            if (c instanceof JRootPane) {
                root = (JRootPane)(JRootPane)c;
            }
        }
        if (root != null) {
            root.repaint();
        } else {
            c.repaint();
        }
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
