package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.accessibility.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.swing.text.*;
import javax.swing.event.*;
import sun.swing.DefaultLookup;
import sun.swing.UIAction;

class BasicComboBoxUI$Actions extends UIAction {
    private static final String HIDE = "hidePopup";
    private static final String DOWN = "selectNext";
    private static final String DOWN_2 = "selectNext2";
    private static final String TOGGLE = "togglePopup";
    private static final String TOGGLE_2 = "spacePopup";
    private static final String UP = "selectPrevious";
    private static final String UP_2 = "selectPrevious2";
    private static final String ENTER = "enterPressed";
    private static final String PAGE_DOWN = "pageDownPassThrough";
    private static final String PAGE_UP = "pageUpPassThrough";
    private static final String HOME = "homePassThrough";
    private static final String END = "endPassThrough";
    
    BasicComboBoxUI$Actions(String name) {
        super(name);
    }
    
    public void actionPerformed(ActionEvent e) {
        String key = getName();
        JComboBox comboBox = (JComboBox)(JComboBox)e.getSource();
        BasicComboBoxUI ui = (BasicComboBoxUI)(BasicComboBoxUI)BasicLookAndFeel.getUIOfType(comboBox.getUI(), BasicComboBoxUI.class);
        if (key == HIDE) {
            comboBox.firePopupMenuCanceled();
            comboBox.setPopupVisible(false);
        } else if (key == PAGE_DOWN || key == PAGE_UP || key == HOME || key == END) {
            int index = getNextIndex(comboBox, key);
            if (index >= 0 && index < comboBox.getItemCount()) {
                comboBox.setSelectedIndex(index);
            }
        } else if (key == DOWN) {
            if (comboBox.isShowing()) {
                if (comboBox.isPopupVisible()) {
                    if (ui != null) {
                        ui.selectNextPossibleValue();
                    }
                } else {
                    comboBox.setPopupVisible(true);
                }
            }
        } else if (key == DOWN_2) {
            if (comboBox.isShowing()) {
                if ((comboBox.isEditable() || (ui != null && ui.isTableCellEditor())) && !comboBox.isPopupVisible()) {
                    comboBox.setPopupVisible(true);
                } else {
                    if (ui != null) {
                        ui.selectNextPossibleValue();
                    }
                }
            }
        } else if (key == TOGGLE || key == TOGGLE_2) {
            if (ui != null && (key == TOGGLE || !comboBox.isEditable())) {
                if (ui.isTableCellEditor()) {
                    comboBox.setSelectedIndex(ui.popup.getList().getSelectedIndex());
                } else {
                    comboBox.setPopupVisible(!comboBox.isPopupVisible());
                }
            }
        } else if (key == UP) {
            if (ui != null) {
                if (ui.isPopupVisible(comboBox)) {
                    ui.selectPreviousPossibleValue();
                } else if (DefaultLookup.getBoolean(comboBox, ui, "ComboBox.showPopupOnNavigation", false)) {
                    ui.setPopupVisible(comboBox, true);
                }
            }
        } else if (key == UP_2) {
            if (comboBox.isShowing() && ui != null) {
                if (comboBox.isEditable() && !comboBox.isPopupVisible()) {
                    comboBox.setPopupVisible(true);
                } else {
                    ui.selectPreviousPossibleValue();
                }
            }
        } else if (key == ENTER) {
            if (ui != null && ui.isTableCellEditor()) {
                comboBox.setSelectedIndex(ui.popup.getList().getSelectedIndex());
            } else {
                if (comboBox.isPopupVisible()) {
                    comboBox.setPopupVisible(false);
                } else {
                    JRootPane root = SwingUtilities.getRootPane(comboBox);
                    if (root != null) {
                        InputMap im = root.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
                        ActionMap am = root.getActionMap();
                        if (im != null && am != null) {
                            Object obj = im.get(KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, 0));
                            if (obj != null) {
                                Action action = am.get(obj);
                                if (action != null) {
                                    action.actionPerformed(new ActionEvent(root, e.getID(), e.getActionCommand(), e.getWhen(), e.getModifiers()));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    
    private int getNextIndex(JComboBox comboBox, String key) {
        if (key == PAGE_UP) {
            int listHeight = comboBox.getMaximumRowCount();
            int index = comboBox.getSelectedIndex() - listHeight;
            return (index < 0 ? 0 : index);
        } else if (key == PAGE_DOWN) {
            int listHeight = comboBox.getMaximumRowCount();
            int index = comboBox.getSelectedIndex() + listHeight;
            int max = comboBox.getItemCount();
            return (index < max ? index : max - 1);
        } else if (key == HOME) {
            return 0;
        } else if (key == END) {
            return comboBox.getItemCount() - 1;
        }
        return comboBox.getSelectedIndex();
    }
    
    public boolean isEnabled(Object c) {
        if (getName() == HIDE) {
            return (c != null && ((JComboBox)(JComboBox)c).isPopupVisible());
        }
        return true;
    }
}
