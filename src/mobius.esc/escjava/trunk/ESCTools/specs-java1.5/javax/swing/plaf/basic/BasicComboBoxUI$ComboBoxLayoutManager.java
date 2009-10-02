package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.accessibility.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.swing.text.*;
import javax.swing.event.*;

public class BasicComboBoxUI$ComboBoxLayoutManager implements LayoutManager {
    /*synthetic*/ final BasicComboBoxUI this$0;
    
    public BasicComboBoxUI$ComboBoxLayoutManager(/*synthetic*/ final BasicComboBoxUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void addLayoutComponent(String name, Component comp) {
    }
    
    public void removeLayoutComponent(Component comp) {
    }
    
    public Dimension preferredLayoutSize(Container parent) {
        return BasicComboBoxUI.access$100(this$0).preferredLayoutSize(parent);
    }
    
    public Dimension minimumLayoutSize(Container parent) {
        return BasicComboBoxUI.access$100(this$0).minimumLayoutSize(parent);
    }
    
    public void layoutContainer(Container parent) {
        BasicComboBoxUI.access$100(this$0).layoutContainer(parent);
    }
}
