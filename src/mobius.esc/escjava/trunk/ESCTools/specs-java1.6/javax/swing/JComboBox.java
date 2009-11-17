package javax.swing;

import java.beans.*;
import java.util.*;
import java.awt.*;
import java.awt.event.*;
import java.io.ObjectOutputStream;
import java.io.IOException;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.accessibility.*;

public class JComboBox extends JComponent implements ItemSelectable, ListDataListener, ActionListener, Accessible {
    private static final String uiClassID = "ComboBoxUI";
    protected ComboBoxModel dataModel;
    protected ListCellRenderer renderer;
    protected ComboBoxEditor editor;
    protected int maximumRowCount = 8;
    protected boolean isEditable = false;
    protected JComboBox$KeySelectionManager keySelectionManager = null;
    protected String actionCommand = "comboBoxChanged";
    protected boolean lightWeightPopupEnabled = JPopupMenu.getDefaultLightWeightPopupEnabled();
    protected Object selectedItemReminder = null;
    private Object prototypeDisplayValue;
    private boolean firingActionEvent = false;
    private boolean selectingItem = false;
    
    public JComboBox(ComboBoxModel aModel) {
        
        setModel(aModel);
        init();
    }
    
    public JComboBox(final Object[] items) {
        
        setModel(new DefaultComboBoxModel(items));
        init();
    }
    
    public JComboBox(Vector items) {
        
        setModel(new DefaultComboBoxModel(items));
        init();
    }
    
    public JComboBox() {
        
        setModel(new DefaultComboBoxModel());
        init();
    }
    
    private void init() {
        installAncestorListener();
        setOpaque(true);
        updateUI();
    }
    
    protected void installAncestorListener() {
        addAncestorListener(new JComboBox$1(this));
    }
    
    public void setUI(ComboBoxUI ui) {
        super.setUI(ui);
    }
    
    public void updateUI() {
        setUI((ComboBoxUI)(ComboBoxUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public ComboBoxUI getUI() {
        return (ComboBoxUI)(ComboBoxUI)ui;
    }
    
    public void setModel(ComboBoxModel aModel) {
        ComboBoxModel oldModel = dataModel;
        if (oldModel != null) {
            oldModel.removeListDataListener(this);
        }
        dataModel = aModel;
        dataModel.addListDataListener(this);
        selectedItemReminder = dataModel.getSelectedItem();
        firePropertyChange("model", oldModel, dataModel);
    }
    
    public ComboBoxModel getModel() {
        return dataModel;
    }
    
    public void setLightWeightPopupEnabled(boolean aFlag) {
        boolean oldFlag = lightWeightPopupEnabled;
        lightWeightPopupEnabled = aFlag;
        firePropertyChange("lightWeightPopupEnabled", oldFlag, lightWeightPopupEnabled);
    }
    
    public boolean isLightWeightPopupEnabled() {
        return lightWeightPopupEnabled;
    }
    
    public void setEditable(boolean aFlag) {
        boolean oldFlag = isEditable;
        isEditable = aFlag;
        firePropertyChange("editable", oldFlag, isEditable);
    }
    
    public boolean isEditable() {
        return isEditable;
    }
    
    public void setMaximumRowCount(int count) {
        int oldCount = maximumRowCount;
        maximumRowCount = count;
        firePropertyChange("maximumRowCount", oldCount, maximumRowCount);
    }
    
    public int getMaximumRowCount() {
        return maximumRowCount;
    }
    
    public void setRenderer(ListCellRenderer aRenderer) {
        ListCellRenderer oldRenderer = renderer;
        renderer = aRenderer;
        firePropertyChange("renderer", oldRenderer, renderer);
        invalidate();
    }
    
    public ListCellRenderer getRenderer() {
        return renderer;
    }
    
    public void setEditor(ComboBoxEditor anEditor) {
        ComboBoxEditor oldEditor = editor;
        if (editor != null) {
            editor.removeActionListener(this);
        }
        editor = anEditor;
        if (editor != null) {
            editor.addActionListener(this);
        }
        firePropertyChange("editor", oldEditor, editor);
    }
    
    public ComboBoxEditor getEditor() {
        return editor;
    }
    
    public void setSelectedItem(Object anObject) {
        Object oldSelection = selectedItemReminder;
        if (oldSelection == null || !oldSelection.equals(anObject)) {
            if (anObject != null && !isEditable()) {
                boolean found = false;
                for (int i = 0; i < dataModel.getSize(); i++) {
                    if (anObject.equals(dataModel.getElementAt(i))) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    return;
                }
            }
            selectingItem = true;
            dataModel.setSelectedItem(anObject);
            selectingItem = false;
            if (selectedItemReminder != dataModel.getSelectedItem()) {
                selectedItemChanged();
            }
        }
        fireActionEvent();
    }
    
    public Object getSelectedItem() {
        return dataModel.getSelectedItem();
    }
    
    public void setSelectedIndex(int anIndex) {
        int size = dataModel.getSize();
        if (anIndex == -1) {
            setSelectedItem(null);
        } else if (anIndex < -1 || anIndex >= size) {
            throw new IllegalArgumentException("setSelectedIndex: " + anIndex + " out of bounds");
        } else {
            setSelectedItem(dataModel.getElementAt(anIndex));
        }
    }
    
    public int getSelectedIndex() {
        Object sObject = dataModel.getSelectedItem();
        int i;
        int c;
        Object obj;
        for (i = 0, c = dataModel.getSize(); i < c; i++) {
            obj = dataModel.getElementAt(i);
            if (obj != null && obj.equals(sObject)) return i;
        }
        return -1;
    }
    
    public Object getPrototypeDisplayValue() {
        return prototypeDisplayValue;
    }
    
    public void setPrototypeDisplayValue(Object prototypeDisplayValue) {
        Object oldValue = this.prototypeDisplayValue;
        this.prototypeDisplayValue = prototypeDisplayValue;
        firePropertyChange("prototypeDisplayValue", oldValue, prototypeDisplayValue);
    }
    
    public void addItem(Object anObject) {
        checkMutableComboBoxModel();
        ((MutableComboBoxModel)(MutableComboBoxModel)dataModel).addElement(anObject);
    }
    
    public void insertItemAt(Object anObject, int index) {
        checkMutableComboBoxModel();
        ((MutableComboBoxModel)(MutableComboBoxModel)dataModel).insertElementAt(anObject, index);
    }
    
    public void removeItem(Object anObject) {
        checkMutableComboBoxModel();
        ((MutableComboBoxModel)(MutableComboBoxModel)dataModel).removeElement(anObject);
    }
    
    public void removeItemAt(int anIndex) {
        checkMutableComboBoxModel();
        ((MutableComboBoxModel)(MutableComboBoxModel)dataModel).removeElementAt(anIndex);
    }
    
    public void removeAllItems() {
        checkMutableComboBoxModel();
        MutableComboBoxModel model = (MutableComboBoxModel)(MutableComboBoxModel)dataModel;
        int size = model.getSize();
        if (model instanceof DefaultComboBoxModel) {
            ((DefaultComboBoxModel)(DefaultComboBoxModel)model).removeAllElements();
        } else {
            for (int i = 0; i < size; ++i) {
                Object element = model.getElementAt(0);
                model.removeElement(element);
            }
        }
        selectedItemReminder = null;
        if (isEditable()) {
            editor.setItem(null);
        }
    }
    
    void checkMutableComboBoxModel() {
        if (!(dataModel instanceof MutableComboBoxModel)) throw new RuntimeException("Cannot use this method with a non-Mutable data model.");
    }
    
    public void showPopup() {
        setPopupVisible(true);
    }
    
    public void hidePopup() {
        setPopupVisible(false);
    }
    
    public void setPopupVisible(boolean v) {
        getUI().setPopupVisible(this, v);
    }
    
    public boolean isPopupVisible() {
        return getUI().isPopupVisible(this);
    }
    
    public void addItemListener(ItemListener aListener) {
        listenerList.add(ItemListener.class, aListener);
    }
    
    public void removeItemListener(ItemListener aListener) {
        listenerList.remove(ItemListener.class, aListener);
    }
    
    public ItemListener[] getItemListeners() {
        return (ItemListener[])(ItemListener[])listenerList.getListeners(ItemListener.class);
    }
    
    public void addActionListener(ActionListener l) {
        listenerList.add(ActionListener.class, l);
    }
    
    public void removeActionListener(ActionListener l) {
        if ((l != null) && (getAction() == l)) {
            setAction(null);
        } else {
            listenerList.remove(ActionListener.class, l);
        }
    }
    
    public ActionListener[] getActionListeners() {
        return (ActionListener[])(ActionListener[])listenerList.getListeners(ActionListener.class);
    }
    
    public void addPopupMenuListener(PopupMenuListener l) {
        listenerList.add(PopupMenuListener.class, l);
    }
    
    public void removePopupMenuListener(PopupMenuListener l) {
        listenerList.remove(PopupMenuListener.class, l);
    }
    
    public PopupMenuListener[] getPopupMenuListeners() {
        return (PopupMenuListener[])(PopupMenuListener[])listenerList.getListeners(PopupMenuListener.class);
    }
    
    public void firePopupMenuWillBecomeVisible() {
        Object[] listeners = listenerList.getListenerList();
        PopupMenuEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == PopupMenuListener.class) {
                if (e == null) e = new PopupMenuEvent(this);
                ((PopupMenuListener)(PopupMenuListener)listeners[i + 1]).popupMenuWillBecomeVisible(e);
            }
        }
    }
    
    public void firePopupMenuWillBecomeInvisible() {
        Object[] listeners = listenerList.getListenerList();
        PopupMenuEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == PopupMenuListener.class) {
                if (e == null) e = new PopupMenuEvent(this);
                ((PopupMenuListener)(PopupMenuListener)listeners[i + 1]).popupMenuWillBecomeInvisible(e);
            }
        }
    }
    
    public void firePopupMenuCanceled() {
        Object[] listeners = listenerList.getListenerList();
        PopupMenuEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == PopupMenuListener.class) {
                if (e == null) e = new PopupMenuEvent(this);
                ((PopupMenuListener)(PopupMenuListener)listeners[i + 1]).popupMenuCanceled(e);
            }
        }
    }
    
    public void setActionCommand(String aCommand) {
        actionCommand = aCommand;
    }
    
    public String getActionCommand() {
        return actionCommand;
    }
    private Action action;
    private PropertyChangeListener actionPropertyChangeListener;
    
    public void setAction(Action a) {
        Action oldValue = getAction();
        if (action == null || !action.equals(a)) {
            action = a;
            if (oldValue != null) {
                removeActionListener(oldValue);
                oldValue.removePropertyChangeListener(actionPropertyChangeListener);
                actionPropertyChangeListener = null;
            }
            configurePropertiesFromAction(action);
            if (action != null) {
                if (!isListener(ActionListener.class, action)) {
                    addActionListener(action);
                }
                actionPropertyChangeListener = createActionPropertyChangeListener(action);
                action.addPropertyChangeListener(actionPropertyChangeListener);
            }
            firePropertyChange("action", oldValue, action);
            revalidate();
            repaint();
        }
    }
    
    private boolean isListener(Class c, ActionListener a) {
        boolean isListener = false;
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == c && listeners[i + 1] == a) {
                isListener = true;
            }
        }
        return isListener;
    }
    
    public Action getAction() {
        return action;
    }
    
    protected void configurePropertiesFromAction(Action a) {
        setEnabled((a != null ? a.isEnabled() : true));
        setToolTipText((a != null ? (String)(String)a.getValue(Action.SHORT_DESCRIPTION) : null));
    }
    
    protected PropertyChangeListener createActionPropertyChangeListener(Action a) {
        return new JComboBox$2(this, this, a);
    }
    
    protected void fireItemStateChanged(ItemEvent e) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ItemListener.class) {
                ((ItemListener)(ItemListener)listeners[i + 1]).itemStateChanged(e);
            }
        }
    }
    
    protected void fireActionEvent() {
        if (!firingActionEvent) {
            firingActionEvent = true;
            ActionEvent e = null;
            Object[] listeners = listenerList.getListenerList();
            long mostRecentEventTime = EventQueue.getMostRecentEventTime();
            int modifiers = 0;
            AWTEvent currentEvent = EventQueue.getCurrentEvent();
            if (currentEvent instanceof InputEvent) {
                modifiers = ((InputEvent)(InputEvent)currentEvent).getModifiers();
            } else if (currentEvent instanceof ActionEvent) {
                modifiers = ((ActionEvent)(ActionEvent)currentEvent).getModifiers();
            }
            for (int i = listeners.length - 2; i >= 0; i -= 2) {
                if (listeners[i] == ActionListener.class) {
                    if (e == null) e = new ActionEvent(this, ActionEvent.ACTION_PERFORMED, getActionCommand(), mostRecentEventTime, modifiers);
                    ((ActionListener)(ActionListener)listeners[i + 1]).actionPerformed(e);
                }
            }
            firingActionEvent = false;
        }
    }
    
    protected void selectedItemChanged() {
        if (selectedItemReminder != null) {
            fireItemStateChanged(new ItemEvent(this, ItemEvent.ITEM_STATE_CHANGED, selectedItemReminder, ItemEvent.DESELECTED));
        }
        selectedItemReminder = dataModel.getSelectedItem();
        if (selectedItemReminder != null) {
            fireItemStateChanged(new ItemEvent(this, ItemEvent.ITEM_STATE_CHANGED, selectedItemReminder, ItemEvent.SELECTED));
        }
    }
    
    public Object[] getSelectedObjects() {
        Object selectedObject = getSelectedItem();
        if (selectedObject == null) return new Object[0]; else {
            Object[] result = new Object[1];
            result[0] = selectedObject;
            return result;
        }
    }
    
    public void actionPerformed(ActionEvent e) {
        Object newItem = getEditor().getItem();
        setPopupVisible(false);
        getModel().setSelectedItem(newItem);
        String oldCommand = getActionCommand();
        setActionCommand("comboBoxEdited");
        fireActionEvent();
        setActionCommand(oldCommand);
    }
    
    public void contentsChanged(ListDataEvent e) {
        Object oldSelection = selectedItemReminder;
        Object newSelection = dataModel.getSelectedItem();
        if (oldSelection == null || !oldSelection.equals(newSelection)) {
            selectedItemChanged();
            if (!selectingItem) {
                fireActionEvent();
            }
        }
    }
    
    public void intervalAdded(ListDataEvent e) {
        if (selectedItemReminder != dataModel.getSelectedItem()) {
            selectedItemChanged();
        }
    }
    
    public void intervalRemoved(ListDataEvent e) {
        contentsChanged(e);
    }
    
    public boolean selectWithKeyChar(char keyChar) {
        int index;
        if (keySelectionManager == null) keySelectionManager = createDefaultKeySelectionManager();
        index = keySelectionManager.selectionForKey(keyChar, getModel());
        if (index != -1) {
            setSelectedIndex(index);
            return true;
        } else return false;
    }
    
    public void setEnabled(boolean b) {
        super.setEnabled(b);
        firePropertyChange("enabled", !isEnabled(), isEnabled());
    }
    
    public void configureEditor(ComboBoxEditor anEditor, Object anItem) {
        anEditor.setItem(anItem);
    }
    
    public void processKeyEvent(KeyEvent e) {
        if (e.getKeyCode() == KeyEvent.VK_TAB) {
            hidePopup();
        }
        super.processKeyEvent(e);
    }
    
    public void setKeySelectionManager(JComboBox$KeySelectionManager aManager) {
        keySelectionManager = aManager;
    }
    
    public JComboBox$KeySelectionManager getKeySelectionManager() {
        return keySelectionManager;
    }
    
    public int getItemCount() {
        return dataModel.getSize();
    }
    
    public Object getItemAt(int index) {
        return dataModel.getElementAt(index);
    }
    
    protected JComboBox$KeySelectionManager createDefaultKeySelectionManager() {
        return new JComboBox$DefaultKeySelectionManager(this);
    }
    {
    }
    {
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if (getUIClassID().equals(uiClassID)) {
            byte count = JComponent.getWriteObjCounter(this);
            JComponent.setWriteObjCounter(this, --count);
            if (count == 0 && ui != null) {
                ui.installUI(this);
            }
        }
    }
    
    protected String paramString() {
        String selectedItemReminderString = (selectedItemReminder != null ? selectedItemReminder.toString() : "");
        String isEditableString = (isEditable ? "true" : "false");
        String lightWeightPopupEnabledString = (lightWeightPopupEnabled ? "true" : "false");
        return super.paramString() + ",isEditable=" + isEditableString + ",lightWeightPopupEnabled=" + lightWeightPopupEnabledString + ",maximumRowCount=" + maximumRowCount + ",selectedItemReminder=" + selectedItemReminderString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JComboBox$AccessibleJComboBox(this);
        }
        return accessibleContext;
    }
    {
    }
}
