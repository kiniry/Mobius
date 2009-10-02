package javax.swing;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Container;
import java.awt.Dialog;
import java.awt.Dimension;
import java.awt.KeyboardFocusManager;
import java.awt.Frame;
import java.awt.Point;
import java.awt.HeadlessException;
import java.awt.Window;
import java.awt.event.WindowListener;
import java.awt.event.WindowAdapter;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.lang.reflect.Method;
import java.lang.reflect.InvocationTargetException;
import java.security.AccessController;
import java.util.Vector;
import javax.swing.plaf.OptionPaneUI;
import javax.accessibility.*;

public class JOptionPane extends JComponent implements Accessible {
    private static final String uiClassID = "OptionPaneUI";
    public static final Object UNINITIALIZED_VALUE = "uninitializedValue";
    public static final int DEFAULT_OPTION = -1;
    public static final int YES_NO_OPTION = 0;
    public static final int YES_NO_CANCEL_OPTION = 1;
    public static final int OK_CANCEL_OPTION = 2;
    public static final int YES_OPTION = 0;
    public static final int NO_OPTION = 1;
    public static final int CANCEL_OPTION = 2;
    public static final int OK_OPTION = 0;
    public static final int CLOSED_OPTION = -1;
    public static final int ERROR_MESSAGE = 0;
    public static final int INFORMATION_MESSAGE = 1;
    public static final int WARNING_MESSAGE = 2;
    public static final int QUESTION_MESSAGE = 3;
    public static final int PLAIN_MESSAGE = -1;
    public static final String ICON_PROPERTY = "icon";
    public static final String MESSAGE_PROPERTY = "message";
    public static final String VALUE_PROPERTY = "value";
    public static final String OPTIONS_PROPERTY = "options";
    public static final String INITIAL_VALUE_PROPERTY = "initialValue";
    public static final String MESSAGE_TYPE_PROPERTY = "messageType";
    public static final String OPTION_TYPE_PROPERTY = "optionType";
    public static final String SELECTION_VALUES_PROPERTY = "selectionValues";
    public static final String INITIAL_SELECTION_VALUE_PROPERTY = "initialSelectionValue";
    public static final String INPUT_VALUE_PROPERTY = "inputValue";
    public static final String WANTS_INPUT_PROPERTY = "wantsInput";
    protected transient Icon icon;
    protected transient Object message;
    protected transient Object[] options;
    protected transient Object initialValue;
    protected int messageType;
    protected int optionType;
    protected transient Object value;
    protected transient Object[] selectionValues;
    protected transient Object inputValue;
    protected transient Object initialSelectionValue;
    protected boolean wantsInput;
    
    public static String showInputDialog(Object message) throws HeadlessException {
        return showInputDialog(null, message);
    }
    
    public static String showInputDialog(Object message, Object initialSelectionValue) {
        return showInputDialog(null, message, initialSelectionValue);
    }
    
    public static String showInputDialog(Component parentComponent, Object message) throws HeadlessException {
        return showInputDialog(parentComponent, message, UIManager.getString("OptionPane.inputDialogTitle", parentComponent), QUESTION_MESSAGE);
    }
    
    public static String showInputDialog(Component parentComponent, Object message, Object initialSelectionValue) {
        return (String)(String)showInputDialog(parentComponent, message, UIManager.getString("OptionPane.inputDialogTitle", parentComponent), QUESTION_MESSAGE, null, null, initialSelectionValue);
    }
    
    public static String showInputDialog(Component parentComponent, Object message, String title, int messageType) throws HeadlessException {
        return (String)(String)showInputDialog(parentComponent, message, title, messageType, null, null, null);
    }
    
    public static Object showInputDialog(Component parentComponent, Object message, String title, int messageType, Icon icon, Object[] selectionValues, Object initialSelectionValue) throws HeadlessException {
        JOptionPane pane = new JOptionPane(message, messageType, OK_CANCEL_OPTION, icon, null, null);
        pane.setWantsInput(true);
        pane.setSelectionValues(selectionValues);
        pane.setInitialSelectionValue(initialSelectionValue);
        pane.setComponentOrientation(((parentComponent == null) ? getRootFrame() : parentComponent).getComponentOrientation());
        int style = styleFromMessageType(messageType);
        JDialog dialog = pane.createDialog(parentComponent, title, style);
        pane.selectInitialValue();
        dialog.show();
        dialog.dispose();
        Object value = pane.getInputValue();
        if (value == UNINITIALIZED_VALUE) {
            return null;
        }
        return value;
    }
    
    public static void showMessageDialog(Component parentComponent, Object message) throws HeadlessException {
        showMessageDialog(parentComponent, message, UIManager.getString("OptionPane.messageDialogTitle", parentComponent), INFORMATION_MESSAGE);
    }
    
    public static void showMessageDialog(Component parentComponent, Object message, String title, int messageType) throws HeadlessException {
        showMessageDialog(parentComponent, message, title, messageType, null);
    }
    
    public static void showMessageDialog(Component parentComponent, Object message, String title, int messageType, Icon icon) throws HeadlessException {
        showOptionDialog(parentComponent, message, title, DEFAULT_OPTION, messageType, icon, null, null);
    }
    
    public static int showConfirmDialog(Component parentComponent, Object message) throws HeadlessException {
        return showConfirmDialog(parentComponent, message, UIManager.getString("OptionPane.titleText"), YES_NO_CANCEL_OPTION);
    }
    
    public static int showConfirmDialog(Component parentComponent, Object message, String title, int optionType) throws HeadlessException {
        return showConfirmDialog(parentComponent, message, title, optionType, QUESTION_MESSAGE);
    }
    
    public static int showConfirmDialog(Component parentComponent, Object message, String title, int optionType, int messageType) throws HeadlessException {
        return showConfirmDialog(parentComponent, message, title, optionType, messageType, null);
    }
    
    public static int showConfirmDialog(Component parentComponent, Object message, String title, int optionType, int messageType, Icon icon) throws HeadlessException {
        return showOptionDialog(parentComponent, message, title, optionType, messageType, icon, null, null);
    }
    
    public static int showOptionDialog(Component parentComponent, Object message, String title, int optionType, int messageType, Icon icon, Object[] options, Object initialValue) throws HeadlessException {
        JOptionPane pane = new JOptionPane(message, messageType, optionType, icon, options, initialValue);
        pane.setInitialValue(initialValue);
        pane.setComponentOrientation(((parentComponent == null) ? getRootFrame() : parentComponent).getComponentOrientation());
        int style = styleFromMessageType(messageType);
        JDialog dialog = pane.createDialog(parentComponent, title, style);
        pane.selectInitialValue();
        dialog.show();
        dialog.dispose();
        Object selectedValue = pane.getValue();
        if (selectedValue == null) return CLOSED_OPTION;
        if (options == null) {
            if (selectedValue instanceof Integer) return ((Integer)(Integer)selectedValue).intValue();
            return CLOSED_OPTION;
        }
        for (int counter = 0, maxCounter = options.length; counter < maxCounter; counter++) {
            if (options[counter].equals(selectedValue)) return counter;
        }
        return CLOSED_OPTION;
    }
    
    public JDialog createDialog(Component parentComponent, String title) throws HeadlessException {
        int style = styleFromMessageType(getMessageType());
        return createDialog(parentComponent, title, style);
    }
    
    private JDialog createDialog(Component parentComponent, String title, int style) throws HeadlessException {
        final JDialog dialog;
        Window window = JOptionPane.getWindowForComponent(parentComponent);
        if (window instanceof Frame) {
            dialog = new JDialog((Frame)(Frame)window, title, true);
        } else {
            dialog = new JDialog((Dialog)(Dialog)window, title, true);
        }
        dialog.setComponentOrientation(this.getComponentOrientation());
        if (window instanceof SwingUtilities$SharedOwnerFrame) {
            WindowListener ownerShutdownListener = (WindowListener)SwingUtilities.getSharedOwnerFrameShutdownListener();
            dialog.addWindowListener(ownerShutdownListener);
        }
        Container contentPane = dialog.getContentPane();
        contentPane.setLayout(new BorderLayout());
        contentPane.add(this, BorderLayout.CENTER);
        dialog.setResizable(false);
        if (JDialog.isDefaultLookAndFeelDecorated()) {
            boolean supportsWindowDecorations = UIManager.getLookAndFeel().getSupportsWindowDecorations();
            if (supportsWindowDecorations) {
                dialog.setUndecorated(true);
                getRootPane().setWindowDecorationStyle(style);
            }
        }
        dialog.pack();
        dialog.setLocationRelativeTo(parentComponent);
        WindowAdapter adapter = new JOptionPane$1(this);
        dialog.addWindowListener(adapter);
        dialog.addWindowFocusListener(adapter);
        dialog.addComponentListener(new JOptionPane$2(this));
        addPropertyChangeListener(new JOptionPane$3(this, dialog));
        return dialog;
    }
    
    public static void showInternalMessageDialog(Component parentComponent, Object message) {
        showInternalMessageDialog(parentComponent, message, UIManager.getString("OptionPane.messageDialogTitle", parentComponent), INFORMATION_MESSAGE);
    }
    
    public static void showInternalMessageDialog(Component parentComponent, Object message, String title, int messageType) {
        showInternalMessageDialog(parentComponent, message, title, messageType, null);
    }
    
    public static void showInternalMessageDialog(Component parentComponent, Object message, String title, int messageType, Icon icon) {
        showInternalOptionDialog(parentComponent, message, title, DEFAULT_OPTION, messageType, icon, null, null);
    }
    
    public static int showInternalConfirmDialog(Component parentComponent, Object message) {
        return showInternalConfirmDialog(parentComponent, message, UIManager.getString("OptionPane.titleText"), YES_NO_CANCEL_OPTION);
    }
    
    public static int showInternalConfirmDialog(Component parentComponent, Object message, String title, int optionType) {
        return showInternalConfirmDialog(parentComponent, message, title, optionType, QUESTION_MESSAGE);
    }
    
    public static int showInternalConfirmDialog(Component parentComponent, Object message, String title, int optionType, int messageType) {
        return showInternalConfirmDialog(parentComponent, message, title, optionType, messageType, null);
    }
    
    public static int showInternalConfirmDialog(Component parentComponent, Object message, String title, int optionType, int messageType, Icon icon) {
        return showInternalOptionDialog(parentComponent, message, title, optionType, messageType, icon, null, null);
    }
    
    public static int showInternalOptionDialog(Component parentComponent, Object message, String title, int optionType, int messageType, Icon icon, Object[] options, Object initialValue) {
        JOptionPane pane = new JOptionPane(message, messageType, optionType, icon, options, initialValue);
        pane.putClientProperty(PopupFactory.forceHeavyWeightPopupKey, Boolean.TRUE);
        Component fo = KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusOwner();
        pane.setInitialValue(initialValue);
        JInternalFrame dialog = pane.createInternalFrame(parentComponent, title);
        pane.selectInitialValue();
        dialog.setVisible(true);
        if (dialog.isVisible() && !dialog.isShowing()) {
            Container parent = dialog.getParent();
            while (parent != null) {
                if (parent.isVisible() == false) {
                    parent.setVisible(true);
                }
                parent = parent.getParent();
            }
        }
        try {
            Object obj;
            obj = AccessController.doPrivileged(new JOptionPane$ModalPrivilegedAction(Container.class, "startLWModal"));
            if (obj != null) {
                ((Method)(Method)obj).invoke(dialog, null);
            }
        } catch (IllegalAccessException ex) {
        } catch (IllegalArgumentException ex) {
        } catch (InvocationTargetException ex) {
        }
        if (parentComponent instanceof JInternalFrame) {
            try {
                ((JInternalFrame)(JInternalFrame)parentComponent).setSelected(true);
            } catch (java.beans.PropertyVetoException e) {
            }
        }
        Object selectedValue = pane.getValue();
        if (fo != null && fo.isShowing()) {
            fo.requestFocus();
        }
        if (selectedValue == null) {
            return CLOSED_OPTION;
        }
        if (options == null) {
            if (selectedValue instanceof Integer) {
                return ((Integer)(Integer)selectedValue).intValue();
            }
            return CLOSED_OPTION;
        }
        for (int counter = 0, maxCounter = options.length; counter < maxCounter; counter++) {
            if (options[counter].equals(selectedValue)) {
                return counter;
            }
        }
        return CLOSED_OPTION;
    }
    
    public static String showInternalInputDialog(Component parentComponent, Object message) {
        return showInternalInputDialog(parentComponent, message, UIManager.getString("OptionPane.inputDialogTitle", parentComponent), QUESTION_MESSAGE);
    }
    
    public static String showInternalInputDialog(Component parentComponent, Object message, String title, int messageType) {
        return (String)(String)showInternalInputDialog(parentComponent, message, title, messageType, null, null, null);
    }
    
    public static Object showInternalInputDialog(Component parentComponent, Object message, String title, int messageType, Icon icon, Object[] selectionValues, Object initialSelectionValue) {
        JOptionPane pane = new JOptionPane(message, messageType, OK_CANCEL_OPTION, icon, null, null);
        pane.putClientProperty(PopupFactory.forceHeavyWeightPopupKey, Boolean.TRUE);
        Component fo = KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusOwner();
        pane.setWantsInput(true);
        pane.setSelectionValues(selectionValues);
        pane.setInitialSelectionValue(initialSelectionValue);
        JInternalFrame dialog = pane.createInternalFrame(parentComponent, title);
        pane.selectInitialValue();
        dialog.setVisible(true);
        if (dialog.isVisible() && !dialog.isShowing()) {
            Container parent = dialog.getParent();
            while (parent != null) {
                if (parent.isVisible() == false) {
                    parent.setVisible(true);
                }
                parent = parent.getParent();
            }
        }
        try {
            Object obj;
            obj = AccessController.doPrivileged(new JOptionPane$ModalPrivilegedAction(Container.class, "startLWModal"));
            if (obj != null) {
                ((Method)(Method)obj).invoke(dialog, null);
            }
        } catch (IllegalAccessException ex) {
        } catch (IllegalArgumentException ex) {
        } catch (InvocationTargetException ex) {
        }
        if (parentComponent instanceof JInternalFrame) {
            try {
                ((JInternalFrame)(JInternalFrame)parentComponent).setSelected(true);
            } catch (java.beans.PropertyVetoException e) {
            }
        }
        if (fo != null && fo.isShowing()) {
            fo.requestFocus();
        }
        Object value = pane.getInputValue();
        if (value == UNINITIALIZED_VALUE) {
            return null;
        }
        return value;
    }
    
    public JInternalFrame createInternalFrame(Component parentComponent, String title) {
        Container parent = JOptionPane.getDesktopPaneForComponent(parentComponent);
        if (parent == null && (parentComponent == null || (parent = parentComponent.getParent()) == null)) {
            throw new RuntimeException("JOptionPane: parentComponent does not have a valid parent");
        }
        final JInternalFrame iFrame = new JInternalFrame(title, false, true, false, false);
        iFrame.putClientProperty("JInternalFrame.frameType", "optionDialog");
        iFrame.putClientProperty("JInternalFrame.messageType", new Integer(getMessageType()));
        iFrame.addInternalFrameListener(new JOptionPane$4(this));
        addPropertyChangeListener(new JOptionPane$5(this, iFrame));
        iFrame.getContentPane().add(this, BorderLayout.CENTER);
        if (parent instanceof JDesktopPane) {
            parent.add(iFrame, JLayeredPane.MODAL_LAYER);
        } else {
            parent.add(iFrame, BorderLayout.CENTER);
        }
        Dimension iFrameSize = iFrame.getPreferredSize();
        Dimension rootSize = parent.getSize();
        Dimension parentSize = parentComponent.getSize();
        iFrame.setBounds((rootSize.width - iFrameSize.width) / 2, (rootSize.height - iFrameSize.height) / 2, iFrameSize.width, iFrameSize.height);
        Point iFrameCoord = SwingUtilities.convertPoint(parentComponent, 0, 0, parent);
        int x = (parentSize.width - iFrameSize.width) / 2 + iFrameCoord.x;
        int y = (parentSize.height - iFrameSize.height) / 2 + iFrameCoord.y;
        int ovrx = x + iFrameSize.width - rootSize.width;
        int ovry = y + iFrameSize.height - rootSize.height;
        x = Math.max((ovrx > 0 ? x - ovrx : x), 0);
        y = Math.max((ovry > 0 ? y - ovry : y), 0);
        iFrame.setBounds(x, y, iFrameSize.width, iFrameSize.height);
        parent.validate();
        try {
            iFrame.setSelected(true);
        } catch (java.beans.PropertyVetoException e) {
        }
        return iFrame;
    }
    
    public static Frame getFrameForComponent(Component parentComponent) throws HeadlessException {
        if (parentComponent == null) return getRootFrame();
        if (parentComponent instanceof Frame) return (Frame)(Frame)parentComponent;
        return JOptionPane.getFrameForComponent(parentComponent.getParent());
    }
    
    static Window getWindowForComponent(Component parentComponent) throws HeadlessException {
        if (parentComponent == null) return getRootFrame();
        if (parentComponent instanceof Frame || parentComponent instanceof Dialog) return (Window)(Window)parentComponent;
        return JOptionPane.getWindowForComponent(parentComponent.getParent());
    }
    
    public static JDesktopPane getDesktopPaneForComponent(Component parentComponent) {
        if (parentComponent == null) return null;
        if (parentComponent instanceof JDesktopPane) return (JDesktopPane)(JDesktopPane)parentComponent;
        return getDesktopPaneForComponent(parentComponent.getParent());
    }
    private static final Object sharedFrameKey = JOptionPane.class;
    
    public static void setRootFrame(Frame newRootFrame) {
        if (newRootFrame != null) {
            SwingUtilities.appContextPut(sharedFrameKey, newRootFrame);
        } else {
            SwingUtilities.appContextRemove(sharedFrameKey);
        }
    }
    
    public static Frame getRootFrame() throws HeadlessException {
        Frame sharedFrame = (Frame)(Frame)SwingUtilities.appContextGet(sharedFrameKey);
        if (sharedFrame == null) {
            sharedFrame = SwingUtilities.getSharedOwnerFrame();
            SwingUtilities.appContextPut(sharedFrameKey, sharedFrame);
        }
        return sharedFrame;
    }
    
    public JOptionPane() {
        this("JOptionPane message");
    }
    
    public JOptionPane(Object message) {
        this(message, PLAIN_MESSAGE);
    }
    
    public JOptionPane(Object message, int messageType) {
        this(message, messageType, DEFAULT_OPTION);
    }
    
    public JOptionPane(Object message, int messageType, int optionType) {
        this(message, messageType, optionType, null);
    }
    
    public JOptionPane(Object message, int messageType, int optionType, Icon icon) {
        this(message, messageType, optionType, icon, null);
    }
    
    public JOptionPane(Object message, int messageType, int optionType, Icon icon, Object[] options) {
        this(message, messageType, optionType, icon, options, null);
    }
    
    public JOptionPane(Object message, int messageType, int optionType, Icon icon, Object[] options, Object initialValue) {
        
        this.message = message;
        this.options = options;
        this.initialValue = initialValue;
        this.icon = icon;
        setMessageType(messageType);
        setOptionType(optionType);
        value = UNINITIALIZED_VALUE;
        inputValue = UNINITIALIZED_VALUE;
        updateUI();
    }
    
    public void setUI(OptionPaneUI ui) {
        if ((OptionPaneUI)(OptionPaneUI)this.ui != ui) {
            super.setUI(ui);
            invalidate();
        }
    }
    
    public OptionPaneUI getUI() {
        return (OptionPaneUI)(OptionPaneUI)ui;
    }
    
    public void updateUI() {
        setUI((OptionPaneUI)(OptionPaneUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public void setMessage(Object newMessage) {
        Object oldMessage = message;
        message = newMessage;
        firePropertyChange(MESSAGE_PROPERTY, oldMessage, message);
    }
    
    public Object getMessage() {
        return message;
    }
    
    public void setIcon(Icon newIcon) {
        Object oldIcon = icon;
        icon = newIcon;
        firePropertyChange(ICON_PROPERTY, oldIcon, icon);
    }
    
    public Icon getIcon() {
        return icon;
    }
    
    public void setValue(Object newValue) {
        Object oldValue = value;
        value = newValue;
        firePropertyChange(VALUE_PROPERTY, oldValue, value);
    }
    
    public Object getValue() {
        return value;
    }
    
    public void setOptions(Object[] newOptions) {
        Object[] oldOptions = options;
        options = newOptions;
        firePropertyChange(OPTIONS_PROPERTY, oldOptions, options);
    }
    
    public Object[] getOptions() {
        if (options != null) {
            int optionCount = options.length;
            Object[] retOptions = new Object[optionCount];
            System.arraycopy(options, 0, retOptions, 0, optionCount);
            return retOptions;
        }
        return options;
    }
    
    public void setInitialValue(Object newInitialValue) {
        Object oldIV = initialValue;
        initialValue = newInitialValue;
        firePropertyChange(INITIAL_VALUE_PROPERTY, oldIV, initialValue);
    }
    
    public Object getInitialValue() {
        return initialValue;
    }
    
    public void setMessageType(int newType) {
        if (newType != ERROR_MESSAGE && newType != INFORMATION_MESSAGE && newType != WARNING_MESSAGE && newType != QUESTION_MESSAGE && newType != PLAIN_MESSAGE) throw new RuntimeException("JOptionPane: type must be one of JOptionPane.ERROR_MESSAGE, JOptionPane.INFORMATION_MESSAGE, JOptionPane.WARNING_MESSAGE, JOptionPane.QUESTION_MESSAGE or JOptionPane.PLAIN_MESSAGE");
        int oldType = messageType;
        messageType = newType;
        firePropertyChange(MESSAGE_TYPE_PROPERTY, oldType, messageType);
    }
    
    public int getMessageType() {
        return messageType;
    }
    
    public void setOptionType(int newType) {
        if (newType != DEFAULT_OPTION && newType != YES_NO_OPTION && newType != YES_NO_CANCEL_OPTION && newType != OK_CANCEL_OPTION) throw new RuntimeException("JOptionPane: option type must be one of JOptionPane.DEFAULT_OPTION, JOptionPane.YES_NO_OPTION, JOptionPane.YES_NO_CANCEL_OPTION or JOptionPane.OK_CANCEL_OPTION");
        int oldType = optionType;
        optionType = newType;
        firePropertyChange(OPTION_TYPE_PROPERTY, oldType, optionType);
    }
    
    public int getOptionType() {
        return optionType;
    }
    
    public void setSelectionValues(Object[] newValues) {
        Object[] oldValues = selectionValues;
        selectionValues = newValues;
        firePropertyChange(SELECTION_VALUES_PROPERTY, oldValues, newValues);
        if (selectionValues != null) setWantsInput(true);
    }
    
    public Object[] getSelectionValues() {
        return selectionValues;
    }
    
    public void setInitialSelectionValue(Object newValue) {
        Object oldValue = initialSelectionValue;
        initialSelectionValue = newValue;
        firePropertyChange(INITIAL_SELECTION_VALUE_PROPERTY, oldValue, newValue);
    }
    
    public Object getInitialSelectionValue() {
        return initialSelectionValue;
    }
    
    public void setInputValue(Object newValue) {
        Object oldValue = inputValue;
        inputValue = newValue;
        firePropertyChange(INPUT_VALUE_PROPERTY, oldValue, newValue);
    }
    
    public Object getInputValue() {
        return inputValue;
    }
    
    public int getMaxCharactersPerLineCount() {
        return Integer.MAX_VALUE;
    }
    
    public void setWantsInput(boolean newValue) {
        boolean oldValue = wantsInput;
        wantsInput = newValue;
        firePropertyChange(WANTS_INPUT_PROPERTY, oldValue, newValue);
    }
    
    public boolean getWantsInput() {
        return wantsInput;
    }
    
    public void selectInitialValue() {
        OptionPaneUI ui = getUI();
        if (ui != null) {
            ui.selectInitialValue(this);
        }
    }
    
    private static int styleFromMessageType(int messageType) {
        switch (messageType) {
        case ERROR_MESSAGE: 
            return JRootPane.ERROR_DIALOG;
        
        case QUESTION_MESSAGE: 
            return JRootPane.QUESTION_DIALOG;
        
        case WARNING_MESSAGE: 
            return JRootPane.WARNING_DIALOG;
        
        case INFORMATION_MESSAGE: 
            return JRootPane.INFORMATION_DIALOG;
        
        case PLAIN_MESSAGE: 
        
        default: 
            return JRootPane.PLAIN_DIALOG;
        
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        Vector values = new Vector();
        s.defaultWriteObject();
        if (icon != null && icon instanceof Serializable) {
            values.addElement("icon");
            values.addElement(icon);
        }
        if (message != null && message instanceof Serializable) {
            values.addElement("message");
            values.addElement(message);
        }
        if (options != null) {
            Vector serOptions = new Vector();
            for (int counter = 0, maxCounter = options.length; counter < maxCounter; counter++) if (options[counter] instanceof Serializable) serOptions.addElement(options[counter]);
            if (serOptions.size() > 0) {
                int optionCount = serOptions.size();
                Object[] arrayOptions = new Object[optionCount];
                serOptions.copyInto(arrayOptions);
                values.addElement("options");
                values.addElement(arrayOptions);
            }
        }
        if (initialValue != null && initialValue instanceof Serializable) {
            values.addElement("initialValue");
            values.addElement(initialValue);
        }
        if (value != null && value instanceof Serializable) {
            values.addElement("value");
            values.addElement(value);
        }
        if (selectionValues != null) {
            boolean serialize = true;
            for (int counter = 0, maxCounter = selectionValues.length; counter < maxCounter; counter++) {
                if (selectionValues[counter] != null && !(selectionValues[counter] instanceof Serializable)) {
                    serialize = false;
                    break;
                }
            }
            if (serialize) {
                values.addElement("selectionValues");
                values.addElement(selectionValues);
            }
        }
        if (inputValue != null && inputValue instanceof Serializable) {
            values.addElement("inputValue");
            values.addElement(inputValue);
        }
        if (initialSelectionValue != null && initialSelectionValue instanceof Serializable) {
            values.addElement("initialSelectionValue");
            values.addElement(initialSelectionValue);
        }
        s.writeObject(values);
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        Vector values = (Vector)(Vector)s.readObject();
        int indexCounter = 0;
        int maxCounter = values.size();
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("icon")) {
            icon = (Icon)(Icon)values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("message")) {
            message = values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("options")) {
            options = (Object[])(Object[])values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("initialValue")) {
            initialValue = values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("value")) {
            value = values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("selectionValues")) {
            selectionValues = (Object[])(Object[])values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("inputValue")) {
            inputValue = values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("initialSelectionValue")) {
            initialSelectionValue = values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (getUIClassID().equals(uiClassID)) {
            byte count = JComponent.getWriteObjCounter(this);
            JComponent.setWriteObjCounter(this, --count);
            if (count == 0 && ui != null) {
                ui.installUI(this);
            }
        }
    }
    
    protected String paramString() {
        String iconString = (icon != null ? icon.toString() : "");
        String initialValueString = (initialValue != null ? initialValue.toString() : "");
        String messageString = (message != null ? message.toString() : "");
        String messageTypeString;
        if (messageType == ERROR_MESSAGE) {
            messageTypeString = "ERROR_MESSAGE";
        } else if (messageType == INFORMATION_MESSAGE) {
            messageTypeString = "INFORMATION_MESSAGE";
        } else if (messageType == WARNING_MESSAGE) {
            messageTypeString = "WARNING_MESSAGE";
        } else if (messageType == QUESTION_MESSAGE) {
            messageTypeString = "QUESTION_MESSAGE";
        } else if (messageType == PLAIN_MESSAGE) {
            messageTypeString = "PLAIN_MESSAGE";
        } else messageTypeString = "";
        String optionTypeString;
        if (optionType == DEFAULT_OPTION) {
            optionTypeString = "DEFAULT_OPTION";
        } else if (optionType == YES_NO_OPTION) {
            optionTypeString = "YES_NO_OPTION";
        } else if (optionType == YES_NO_CANCEL_OPTION) {
            optionTypeString = "YES_NO_CANCEL_OPTION";
        } else if (optionType == OK_CANCEL_OPTION) {
            optionTypeString = "OK_CANCEL_OPTION";
        } else optionTypeString = "";
        String wantsInputString = (wantsInput ? "true" : "false");
        return super.paramString() + ",icon=" + iconString + ",initialValue=" + initialValueString + ",message=" + messageString + ",messageType=" + messageTypeString + ",optionType=" + optionTypeString + ",wantsInput=" + wantsInputString;
    }
    {
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JOptionPane$AccessibleJOptionPane(this);
        }
        return accessibleContext;
    }
    {
    }
}
