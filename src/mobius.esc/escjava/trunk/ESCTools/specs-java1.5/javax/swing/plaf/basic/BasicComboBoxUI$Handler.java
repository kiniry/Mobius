package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.accessibility.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.swing.text.*;
import javax.swing.event.*;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeEvent;

class BasicComboBoxUI$Handler implements ActionListener, FocusListener, KeyListener, LayoutManager, ListDataListener, PropertyChangeListener {
    
    /*synthetic*/ BasicComboBoxUI$Handler(BasicComboBoxUI x0, javax.swing.plaf.basic.BasicComboBoxUI$1 x1) {
        this(x0);
    }
    /*synthetic*/ final BasicComboBoxUI this$0;
    
    private BasicComboBoxUI$Handler(/*synthetic*/ final BasicComboBoxUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String propertyName = e.getPropertyName();
        JComboBox comboBox = (JComboBox)(JComboBox)e.getSource();
        if (propertyName == "model") {
            ComboBoxModel newModel = (ComboBoxModel)(ComboBoxModel)e.getNewValue();
            ComboBoxModel oldModel = (ComboBoxModel)(ComboBoxModel)e.getOldValue();
            if (oldModel != null && this$0.listDataListener != null) {
                oldModel.removeListDataListener(this$0.listDataListener);
            }
            if (newModel != null && this$0.listDataListener != null) {
                newModel.addListDataListener(this$0.listDataListener);
            }
            if (this$0.editor != null) {
                comboBox.configureEditor(comboBox.getEditor(), comboBox.getSelectedItem());
            }
            this$0.isMinimumSizeDirty = true;
            BasicComboBoxUI.access$202(this$0, true);
            comboBox.revalidate();
            comboBox.repaint();
        } else if (propertyName == "editor" && comboBox.isEditable()) {
            this$0.addEditor();
            comboBox.revalidate();
        } else if (propertyName == "editable") {
            if (comboBox.isEditable()) {
                comboBox.setRequestFocusEnabled(false);
                this$0.addEditor();
            } else {
                comboBox.setRequestFocusEnabled(true);
                this$0.removeEditor();
            }
            BasicComboBoxUI.access$300(this$0);
            comboBox.revalidate();
        } else if (propertyName == "enabled") {
            boolean enabled = comboBox.isEnabled();
            if (this$0.editor != null) this$0.editor.setEnabled(enabled);
            if (this$0.arrowButton != null) this$0.arrowButton.setEnabled(enabled);
            comboBox.repaint();
        } else if (propertyName == "maximumRowCount") {
            if (this$0.isPopupVisible(comboBox)) {
                this$0.setPopupVisible(comboBox, false);
                this$0.setPopupVisible(comboBox, true);
            }
        } else if (propertyName == "font") {
            this$0.listBox.setFont(comboBox.getFont());
            if (this$0.editor != null) {
                this$0.editor.setFont(comboBox.getFont());
            }
            this$0.isMinimumSizeDirty = true;
            comboBox.validate();
        } else if (propertyName == JComponent.TOOL_TIP_TEXT_KEY) {
            BasicComboBoxUI.access$300(this$0);
        } else if (propertyName == "JComboBox.isTableCellEditor") {
            Boolean inTable = (Boolean)(Boolean)e.getNewValue();
            BasicComboBoxUI.access$402(this$0, inTable.equals(Boolean.TRUE) ? true : false);
        } else if (propertyName == "prototypeDisplayValue") {
            this$0.isMinimumSizeDirty = true;
            BasicComboBoxUI.access$202(this$0, true);
            comboBox.revalidate();
        } else if (propertyName == "renderer") {
            this$0.isMinimumSizeDirty = true;
            BasicComboBoxUI.access$202(this$0, true);
            comboBox.revalidate();
        }
    }
    
    public void keyPressed(KeyEvent e) {
        if (BasicComboBoxUI.access$500(this$0, e.getKeyCode(), e.getModifiers())) {
            BasicComboBoxUI.access$602(this$0, 0L);
        } else if (this$0.comboBox.isEnabled() && this$0.comboBox.getModel().getSize() != 0 && isTypeAheadKey(e)) {
            BasicComboBoxUI.access$702(this$0, e.getWhen());
            if (this$0.comboBox.selectWithKeyChar(e.getKeyChar())) {
                e.consume();
            }
        }
    }
    
    public void keyTyped(KeyEvent e) {
    }
    
    public void keyReleased(KeyEvent e) {
    }
    
    private boolean isTypeAheadKey(KeyEvent e) {
        return !e.isAltDown() && !e.isControlDown() && !e.isMetaDown();
    }
    
    public void focusGained(FocusEvent e) {
        if (e.getSource() == this$0.comboBox.getEditor().getEditorComponent()) {
            return;
        }
        this$0.hasFocus = true;
        this$0.comboBox.repaint();
        if (this$0.comboBox.isEditable() && this$0.editor != null) {
            this$0.editor.requestFocus();
        }
    }
    
    public void focusLost(FocusEvent e) {
        if (e.getSource() == this$0.comboBox.getEditor().getEditorComponent()) {
            ComboBoxEditor editor = this$0.comboBox.getEditor();
            Object item = editor.getItem();
            if (!e.isTemporary() && item != null && !item.equals(this$0.comboBox.getSelectedItem())) {
                this$0.comboBox.actionPerformed(new ActionEvent(editor, 0, "", EventQueue.getMostRecentEventTime(), 0));
            }
        }
        this$0.hasFocus = false;
        if (!e.isTemporary()) {
            this$0.setPopupVisible(this$0.comboBox, false);
        }
        this$0.comboBox.repaint();
    }
    
    public void contentsChanged(ListDataEvent e) {
        if (!(e.getIndex0() == -1 && e.getIndex1() == -1)) {
            this$0.isMinimumSizeDirty = true;
            this$0.comboBox.revalidate();
        }
        if (this$0.comboBox.isEditable() && this$0.editor != null) {
            this$0.comboBox.configureEditor(this$0.comboBox.getEditor(), this$0.comboBox.getSelectedItem());
        }
        this$0.comboBox.repaint();
    }
    
    public void intervalAdded(ListDataEvent e) {
        BasicComboBoxUI.access$202(this$0, true);
        contentsChanged(e);
    }
    
    public void intervalRemoved(ListDataEvent e) {
        BasicComboBoxUI.access$202(this$0, true);
        contentsChanged(e);
    }
    
    public void addLayoutComponent(String name, Component comp) {
    }
    
    public void removeLayoutComponent(Component comp) {
    }
    
    public Dimension preferredLayoutSize(Container parent) {
        return parent.getPreferredSize();
    }
    
    public Dimension minimumLayoutSize(Container parent) {
        return parent.getMinimumSize();
    }
    
    public void layoutContainer(Container parent) {
        JComboBox cb = (JComboBox)(JComboBox)parent;
        int width = cb.getWidth();
        int height = cb.getHeight();
        Insets insets = this$0.getInsets();
        int buttonSize = height - (insets.top + insets.bottom);
        Rectangle cvb;
        if (this$0.arrowButton != null) {
            if (BasicGraphicsUtils.isLeftToRight(cb)) {
                this$0.arrowButton.setBounds(width - (insets.right + buttonSize), insets.top, buttonSize, buttonSize);
            } else {
                this$0.arrowButton.setBounds(insets.left, insets.top, buttonSize, buttonSize);
            }
        }
        if (this$0.editor != null) {
            cvb = this$0.rectangleForCurrentValue();
            this$0.editor.setBounds(cvb);
        }
    }
    
    public void actionPerformed(ActionEvent evt) {
        Object item = this$0.comboBox.getEditor().getItem();
        if (item != null && item.equals(this$0.comboBox.getSelectedItem())) {
            ActionMap am = this$0.comboBox.getActionMap();
            if (am != null) {
                Action action = am.get("enterPressed");
                if (action != null) {
                    action.actionPerformed(new ActionEvent(this$0.comboBox, evt.getID(), evt.getActionCommand(), evt.getModifiers()));
                }
            }
        }
    }
}
