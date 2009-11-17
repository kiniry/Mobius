package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeEvent;
import java.io.Serializable;

class BasicComboPopup$Handler implements ItemListener, MouseListener, MouseMotionListener, PropertyChangeListener, Serializable {
    
    /*synthetic*/ BasicComboPopup$Handler(BasicComboPopup x0, javax.swing.plaf.basic.BasicComboPopup$1 x1) {
        this(x0);
    }
    /*synthetic*/ final BasicComboPopup this$0;
    
    private BasicComboPopup$Handler(/*synthetic*/ final BasicComboPopup this$0) {
        this.this$0 = this$0;
        
    }
    
    public void mouseClicked(MouseEvent e) {
    }
    
    public void mousePressed(MouseEvent e) {
        if (e.getSource() == this$0.list) {
            return;
        }
        if (!SwingUtilities.isLeftMouseButton(e) || !this$0.comboBox.isEnabled()) return;
        if (this$0.comboBox.isEditable()) {
            Component comp = this$0.comboBox.getEditor().getEditorComponent();
            if ((!(comp instanceof JComponent)) || ((JComponent)(JComponent)comp).isRequestFocusEnabled()) {
                comp.requestFocus();
            }
        } else if (this$0.comboBox.isRequestFocusEnabled()) {
            this$0.comboBox.requestFocus();
        }
        this$0.togglePopup();
    }
    
    public void mouseReleased(MouseEvent e) {
        if (e.getSource() == this$0.list) {
            this$0.comboBox.setSelectedIndex(this$0.list.getSelectedIndex());
            this$0.comboBox.setPopupVisible(false);
            if (this$0.comboBox.isEditable() && this$0.comboBox.getEditor() != null) {
                this$0.comboBox.configureEditor(this$0.comboBox.getEditor(), this$0.comboBox.getSelectedItem());
            }
            return;
        }
        Component source = (Component)(Component)e.getSource();
        Dimension size = source.getSize();
        Rectangle bounds = new Rectangle(0, 0, size.width - 1, size.height - 1);
        if (!bounds.contains(e.getPoint())) {
            MouseEvent newEvent = this$0.convertMouseEvent(e);
            Point location = newEvent.getPoint();
            Rectangle r = new Rectangle();
            this$0.list.computeVisibleRect(r);
            if (r.contains(location)) {
                this$0.comboBox.setSelectedIndex(this$0.list.getSelectedIndex());
            }
            this$0.comboBox.setPopupVisible(false);
        }
        this$0.hasEntered = false;
        this$0.stopAutoScrolling();
    }
    
    public void mouseEntered(MouseEvent e) {
    }
    
    public void mouseExited(MouseEvent e) {
    }
    
    public void mouseMoved(MouseEvent anEvent) {
        if (anEvent.getSource() == this$0.list) {
            Point location = anEvent.getPoint();
            Rectangle r = new Rectangle();
            this$0.list.computeVisibleRect(r);
            if (r.contains(location)) {
                this$0.updateListBoxSelectionForEvent(anEvent, false);
            }
        }
    }
    
    public void mouseDragged(MouseEvent e) {
        if (e.getSource() == this$0.list) {
            return;
        }
        if (this$0.isVisible()) {
            MouseEvent newEvent = this$0.convertMouseEvent(e);
            Rectangle r = new Rectangle();
            this$0.list.computeVisibleRect(r);
            if (newEvent.getPoint().y >= r.y && newEvent.getPoint().y <= r.y + r.height - 1) {
                this$0.hasEntered = true;
                if (this$0.isAutoScrolling) {
                    this$0.stopAutoScrolling();
                }
                Point location = newEvent.getPoint();
                if (r.contains(location)) {
                    this$0.updateListBoxSelectionForEvent(newEvent, false);
                }
            } else {
                if (this$0.hasEntered) {
                    int directionToScroll = newEvent.getPoint().y < r.y ? 0 : 1;
                    if (this$0.isAutoScrolling && this$0.scrollDirection != directionToScroll) {
                        this$0.stopAutoScrolling();
                        this$0.startAutoScrolling(directionToScroll);
                    } else if (!this$0.isAutoScrolling) {
                        this$0.startAutoScrolling(directionToScroll);
                    }
                } else {
                    if (e.getPoint().y < 0) {
                        this$0.hasEntered = true;
                        this$0.startAutoScrolling(0);
                    }
                }
            }
        }
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        JComboBox comboBox = (JComboBox)(JComboBox)e.getSource();
        String propertyName = e.getPropertyName();
        if (propertyName == "model") {
            ComboBoxModel oldModel = (ComboBoxModel)(ComboBoxModel)e.getOldValue();
            ComboBoxModel newModel = (ComboBoxModel)(ComboBoxModel)e.getNewValue();
            this$0.uninstallComboBoxModelListeners(oldModel);
            this$0.installComboBoxModelListeners(newModel);
            this$0.list.setModel(newModel);
            if (this$0.isVisible()) {
                this$0.hide();
            }
        } else if (propertyName == "renderer") {
            this$0.list.setCellRenderer(comboBox.getRenderer());
            if (this$0.isVisible()) {
                this$0.hide();
            }
        } else if (propertyName == "componentOrientation") {
            ComponentOrientation o = (ComponentOrientation)(ComponentOrientation)e.getNewValue();
            JList list = this$0.getList();
            if (list != null && list.getComponentOrientation() != o) {
                list.setComponentOrientation(o);
            }
            if (this$0.scroller != null && this$0.scroller.getComponentOrientation() != o) {
                this$0.scroller.setComponentOrientation(o);
            }
            if (o != this$0.getComponentOrientation()) {
                this$0.setComponentOrientation(o);
            }
        } else if (propertyName == "lightWeightPopupEnabled") {
            this$0.setLightWeightPopupEnabled(comboBox.isLightWeightPopupEnabled());
        }
    }
    
    public void itemStateChanged(ItemEvent e) {
        if (e.getStateChange() == ItemEvent.SELECTED) {
            JComboBox comboBox = (JComboBox)(JComboBox)e.getSource();
            BasicComboPopup.access$300(this$0, comboBox.getSelectedIndex());
        }
    }
}
