package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import java.awt.Color;

public class BasicBorders {
    
    public BasicBorders() {
        
    }
    
    public static Border getButtonBorder() {
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        Border buttonBorder = new BorderUIResource$CompoundBorderUIResource(new BasicBorders$ButtonBorder(table.getColor("Button.shadow"), table.getColor("Button.darkShadow"), table.getColor("Button.light"), table.getColor("Button.highlight")), new BasicBorders$MarginBorder());
        return buttonBorder;
    }
    
    public static Border getRadioButtonBorder() {
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        Border radioButtonBorder = new BorderUIResource$CompoundBorderUIResource(new BasicBorders$RadioButtonBorder(table.getColor("RadioButton.shadow"), table.getColor("RadioButton.darkShadow"), table.getColor("RadioButton.light"), table.getColor("RadioButton.highlight")), new BasicBorders$MarginBorder());
        return radioButtonBorder;
    }
    
    public static Border getToggleButtonBorder() {
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        Border toggleButtonBorder = new BorderUIResource$CompoundBorderUIResource(new BasicBorders$ToggleButtonBorder(table.getColor("ToggleButton.shadow"), table.getColor("ToggleButton.darkShadow"), table.getColor("ToggleButton.light"), table.getColor("ToggleButton.highlight")), new BasicBorders$MarginBorder());
        return toggleButtonBorder;
    }
    
    public static Border getMenuBarBorder() {
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        Border menuBarBorder = new BasicBorders$MenuBarBorder(table.getColor("MenuBar.shadow"), table.getColor("MenuBar.highlight"));
        return menuBarBorder;
    }
    
    public static Border getSplitPaneBorder() {
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        Border splitPaneBorder = new BasicBorders$SplitPaneBorder(table.getColor("SplitPane.highlight"), table.getColor("SplitPane.darkShadow"));
        return splitPaneBorder;
    }
    
    public static Border getSplitPaneDividerBorder() {
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        Border splitPaneBorder = new BasicBorders$SplitPaneDividerBorder(table.getColor("SplitPane.highlight"), table.getColor("SplitPane.darkShadow"));
        return splitPaneBorder;
    }
    
    public static Border getTextFieldBorder() {
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        Border textFieldBorder = new BasicBorders$FieldBorder(table.getColor("TextField.shadow"), table.getColor("TextField.darkShadow"), table.getColor("TextField.light"), table.getColor("TextField.highlight"));
        return textFieldBorder;
    }
    
    public static Border getProgressBarBorder() {
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        Border progressBarBorder = new BorderUIResource$LineBorderUIResource(Color.green, 2);
        return progressBarBorder;
    }
    
    public static Border getInternalFrameBorder() {
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        Border internalFrameBorder = new BorderUIResource$CompoundBorderUIResource(new BevelBorder(BevelBorder.RAISED, table.getColor("InternalFrame.borderLight"), table.getColor("InternalFrame.borderHighlight"), table.getColor("InternalFrame.borderDarkShadow"), table.getColor("InternalFrame.borderShadow")), BorderFactory.createLineBorder(table.getColor("InternalFrame.borderColor"), 1));
        return internalFrameBorder;
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
