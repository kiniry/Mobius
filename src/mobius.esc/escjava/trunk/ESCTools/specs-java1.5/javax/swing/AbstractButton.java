package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.text.*;
import java.awt.geom.*;
import java.beans.*;
import javax.swing.event.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import javax.swing.text.*;
import javax.swing.text.html.*;
import javax.swing.plaf.basic.*;
import java.util.*;

public abstract class AbstractButton extends JComponent implements ItemSelectable, SwingConstants {
    
    /*synthetic*/ static void access$100(AbstractButton x0) {
        x0.updateMnemonicProperties();
    }
    
    /*synthetic*/ static AbstractButton$Handler access$000(AbstractButton x0) {
        return x0.getHandler();
    }
    
    public AbstractButton() {
        
    }
    public static final String MODEL_CHANGED_PROPERTY = "model";
    public static final String TEXT_CHANGED_PROPERTY = "text";
    public static final String MNEMONIC_CHANGED_PROPERTY = "mnemonic";
    public static final String MARGIN_CHANGED_PROPERTY = "margin";
    public static final String VERTICAL_ALIGNMENT_CHANGED_PROPERTY = "verticalAlignment";
    public static final String HORIZONTAL_ALIGNMENT_CHANGED_PROPERTY = "horizontalAlignment";
    public static final String VERTICAL_TEXT_POSITION_CHANGED_PROPERTY = "verticalTextPosition";
    public static final String HORIZONTAL_TEXT_POSITION_CHANGED_PROPERTY = "horizontalTextPosition";
    public static final String BORDER_PAINTED_CHANGED_PROPERTY = "borderPainted";
    public static final String FOCUS_PAINTED_CHANGED_PROPERTY = "focusPainted";
    public static final String ROLLOVER_ENABLED_CHANGED_PROPERTY = "rolloverEnabled";
    public static final String CONTENT_AREA_FILLED_CHANGED_PROPERTY = "contentAreaFilled";
    public static final String ICON_CHANGED_PROPERTY = "icon";
    public static final String PRESSED_ICON_CHANGED_PROPERTY = "pressedIcon";
    public static final String SELECTED_ICON_CHANGED_PROPERTY = "selectedIcon";
    public static final String ROLLOVER_ICON_CHANGED_PROPERTY = "rolloverIcon";
    public static final String ROLLOVER_SELECTED_ICON_CHANGED_PROPERTY = "rolloverSelectedIcon";
    public static final String DISABLED_ICON_CHANGED_PROPERTY = "disabledIcon";
    public static final String DISABLED_SELECTED_ICON_CHANGED_PROPERTY = "disabledSelectedIcon";
    protected ButtonModel model = null;
    private String text = "";
    private Insets margin = null;
    private Insets defaultMargin = null;
    private Icon defaultIcon = null;
    private Icon pressedIcon = null;
    private Icon disabledIcon = null;
    private Icon selectedIcon = null;
    private Icon disabledSelectedIcon = null;
    private Icon rolloverIcon = null;
    private Icon rolloverSelectedIcon = null;
    private boolean paintBorder = true;
    private boolean paintFocus = true;
    private boolean rolloverEnabled = false;
    private boolean contentAreaFilled = true;
    private int verticalAlignment = CENTER;
    private int horizontalAlignment = CENTER;
    private int verticalTextPosition = CENTER;
    private int horizontalTextPosition = TRAILING;
    private int iconTextGap = 4;
    private int mnemonic;
    private int mnemonicIndex = -1;
    private long multiClickThreshhold = 0;
    private boolean borderPaintedSet = false;
    private boolean rolloverEnabledSet = false;
    private boolean iconTextGapSet = false;
    private boolean contentAreaFilledSet = false;
    private boolean setLayout = false;
    boolean defaultCapable = true;
    private AbstractButton$Handler handler;
    protected ChangeListener changeListener = null;
    protected ActionListener actionListener = null;
    protected ItemListener itemListener = null;
    protected transient ChangeEvent changeEvent;
    
    public String getText() {
        return text;
    }
    
    public void setText(String text) {
        String oldValue = this.text;
        this.text = text;
        firePropertyChange(TEXT_CHANGED_PROPERTY, oldValue, text);
        updateDisplayedMnemonicIndex(text, getMnemonic());
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, oldValue, text);
        }
        if (text == null || oldValue == null || !text.equals(oldValue)) {
            revalidate();
            repaint();
        }
    }
    
    public boolean isSelected() {
        return model.isSelected();
    }
    
    public void setSelected(boolean b) {
        boolean oldValue = isSelected();
        model.setSelected(b);
    }
    
    public void doClick() {
        doClick(68);
    }
    
    public void doClick(int pressTime) {
        Dimension size = getSize();
        model.setArmed(true);
        model.setPressed(true);
        paintImmediately(new Rectangle(0, 0, size.width, size.height));
        try {
            Thread.currentThread().sleep(pressTime);
        } catch (InterruptedException ie) {
        }
        model.setPressed(false);
        model.setArmed(false);
    }
    
    public void setMargin(Insets m) {
        if (m instanceof UIResource) {
            defaultMargin = m;
        } else if (margin instanceof UIResource) {
            defaultMargin = margin;
        }
        if (m == null && defaultMargin != null) {
            m = defaultMargin;
        }
        Insets old = margin;
        margin = m;
        firePropertyChange(MARGIN_CHANGED_PROPERTY, old, m);
        if (old == null || !old.equals(m)) {
            revalidate();
            repaint();
        }
    }
    
    public Insets getMargin() {
        return (margin == null) ? null : (Insets)(Insets)margin.clone();
    }
    
    public Icon getIcon() {
        return defaultIcon;
    }
    
    public void setIcon(Icon defaultIcon) {
        Icon oldValue = this.defaultIcon;
        this.defaultIcon = defaultIcon;
        if (defaultIcon != oldValue && (disabledIcon instanceof UIResource)) {
            disabledIcon = null;
        }
        firePropertyChange(ICON_CHANGED_PROPERTY, oldValue, defaultIcon);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, oldValue, defaultIcon);
        }
        if (defaultIcon != oldValue) {
            if (defaultIcon == null || oldValue == null || defaultIcon.getIconWidth() != oldValue.getIconWidth() || defaultIcon.getIconHeight() != oldValue.getIconHeight()) {
                revalidate();
            }
            repaint();
        }
    }
    
    public Icon getPressedIcon() {
        return pressedIcon;
    }
    
    public void setPressedIcon(Icon pressedIcon) {
        Icon oldValue = this.pressedIcon;
        this.pressedIcon = pressedIcon;
        firePropertyChange(PRESSED_ICON_CHANGED_PROPERTY, oldValue, pressedIcon);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, oldValue, pressedIcon);
        }
        if (pressedIcon != oldValue) {
            if (getModel().isPressed()) {
                repaint();
            }
        }
    }
    
    public Icon getSelectedIcon() {
        return selectedIcon;
    }
    
    public void setSelectedIcon(Icon selectedIcon) {
        Icon oldValue = this.selectedIcon;
        this.selectedIcon = selectedIcon;
        if (selectedIcon != oldValue && disabledSelectedIcon instanceof UIResource) {
            disabledSelectedIcon = null;
        }
        firePropertyChange(SELECTED_ICON_CHANGED_PROPERTY, oldValue, selectedIcon);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, oldValue, selectedIcon);
        }
        if (selectedIcon != oldValue) {
            if (isSelected()) {
                repaint();
            }
        }
    }
    
    public Icon getRolloverIcon() {
        return rolloverIcon;
    }
    
    public void setRolloverIcon(Icon rolloverIcon) {
        Icon oldValue = this.rolloverIcon;
        this.rolloverIcon = rolloverIcon;
        firePropertyChange(ROLLOVER_ICON_CHANGED_PROPERTY, oldValue, rolloverIcon);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, oldValue, rolloverIcon);
        }
        setRolloverEnabled(true);
        if (rolloverIcon != oldValue) {
            repaint();
        }
    }
    
    public Icon getRolloverSelectedIcon() {
        return rolloverSelectedIcon;
    }
    
    public void setRolloverSelectedIcon(Icon rolloverSelectedIcon) {
        Icon oldValue = this.rolloverSelectedIcon;
        this.rolloverSelectedIcon = rolloverSelectedIcon;
        firePropertyChange(ROLLOVER_SELECTED_ICON_CHANGED_PROPERTY, oldValue, rolloverSelectedIcon);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, oldValue, rolloverSelectedIcon);
        }
        setRolloverEnabled(true);
        if (rolloverSelectedIcon != oldValue) {
            if (isSelected()) {
                repaint();
            }
        }
    }
    
    public Icon getDisabledIcon() {
        if (disabledIcon == null) {
            disabledIcon = UIManager.getLookAndFeel().getDisabledIcon(this, getIcon());
            if (disabledIcon != null) {
                firePropertyChange(DISABLED_ICON_CHANGED_PROPERTY, null, disabledIcon);
            }
        }
        return disabledIcon;
    }
    
    public void setDisabledIcon(Icon disabledIcon) {
        Icon oldValue = this.disabledIcon;
        this.disabledIcon = disabledIcon;
        firePropertyChange(DISABLED_ICON_CHANGED_PROPERTY, oldValue, disabledIcon);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, oldValue, disabledIcon);
        }
        if (disabledIcon != oldValue) {
            if (!isEnabled()) {
                repaint();
            }
        }
    }
    
    public Icon getDisabledSelectedIcon() {
        if (disabledSelectedIcon == null) {
            if (selectedIcon != null) {
                disabledSelectedIcon = UIManager.getLookAndFeel().getDisabledSelectedIcon(this, getSelectedIcon());
            } else {
                return getDisabledIcon();
            }
        }
        return disabledSelectedIcon;
    }
    
    public void setDisabledSelectedIcon(Icon disabledSelectedIcon) {
        Icon oldValue = this.disabledSelectedIcon;
        this.disabledSelectedIcon = disabledSelectedIcon;
        firePropertyChange(DISABLED_SELECTED_ICON_CHANGED_PROPERTY, oldValue, disabledSelectedIcon);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, oldValue, disabledSelectedIcon);
        }
        if (disabledSelectedIcon != oldValue) {
            if (disabledSelectedIcon == null || oldValue == null || disabledSelectedIcon.getIconWidth() != oldValue.getIconWidth() || disabledSelectedIcon.getIconHeight() != oldValue.getIconHeight()) {
                revalidate();
            }
            if (!isEnabled() && isSelected()) {
                repaint();
            }
        }
    }
    
    public int getVerticalAlignment() {
        return verticalAlignment;
    }
    
    public void setVerticalAlignment(int alignment) {
        if (alignment == verticalAlignment) return;
        int oldValue = verticalAlignment;
        verticalAlignment = checkVerticalKey(alignment, "verticalAlignment");
        firePropertyChange(VERTICAL_ALIGNMENT_CHANGED_PROPERTY, oldValue, verticalAlignment);
        repaint();
    }
    
    public int getHorizontalAlignment() {
        return horizontalAlignment;
    }
    
    public void setHorizontalAlignment(int alignment) {
        if (alignment == horizontalAlignment) return;
        int oldValue = horizontalAlignment;
        horizontalAlignment = checkHorizontalKey(alignment, "horizontalAlignment");
        firePropertyChange(HORIZONTAL_ALIGNMENT_CHANGED_PROPERTY, oldValue, horizontalAlignment);
        repaint();
    }
    
    public int getVerticalTextPosition() {
        return verticalTextPosition;
    }
    
    public void setVerticalTextPosition(int textPosition) {
        if (textPosition == verticalTextPosition) return;
        int oldValue = verticalTextPosition;
        verticalTextPosition = checkVerticalKey(textPosition, "verticalTextPosition");
        firePropertyChange(VERTICAL_TEXT_POSITION_CHANGED_PROPERTY, oldValue, verticalTextPosition);
        repaint();
    }
    
    public int getHorizontalTextPosition() {
        return horizontalTextPosition;
    }
    
    public void setHorizontalTextPosition(int textPosition) {
        if (textPosition == horizontalTextPosition) return;
        int oldValue = horizontalTextPosition;
        horizontalTextPosition = checkHorizontalKey(textPosition, "horizontalTextPosition");
        firePropertyChange(HORIZONTAL_TEXT_POSITION_CHANGED_PROPERTY, oldValue, horizontalTextPosition);
        repaint();
    }
    
    public int getIconTextGap() {
        return iconTextGap;
    }
    
    public void setIconTextGap(int iconTextGap) {
        int oldValue = this.iconTextGap;
        this.iconTextGap = iconTextGap;
        iconTextGapSet = true;
        firePropertyChange("iconTextGap", oldValue, iconTextGap);
        if (iconTextGap != oldValue) {
            revalidate();
            repaint();
        }
    }
    
    protected int checkHorizontalKey(int key, String exception) {
        if ((key == LEFT) || (key == CENTER) || (key == RIGHT) || (key == LEADING) || (key == TRAILING)) {
            return key;
        } else {
            throw new IllegalArgumentException(exception);
        }
    }
    
    protected int checkVerticalKey(int key, String exception) {
        if ((key == TOP) || (key == CENTER) || (key == BOTTOM)) {
            return key;
        } else {
            throw new IllegalArgumentException(exception);
        }
    }
    
    public void setActionCommand(String actionCommand) {
        getModel().setActionCommand(actionCommand);
    }
    
    public String getActionCommand() {
        String ac = getModel().getActionCommand();
        if (ac == null) {
            ac = getText();
        }
        return ac;
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
        configurePropertiesFromAction(a, null);
    }
    
    void configurePropertiesFromAction(Action a, String[] types) {
        if (types == null) {
            String[] alltypes = {Action.MNEMONIC_KEY, Action.NAME, Action.SHORT_DESCRIPTION, Action.SMALL_ICON, Action.ACTION_COMMAND_KEY, "enabled"};
            types = alltypes;
        }
        for (int i = 0; i < types.length; i++) {
            String type = types[i];
            if (type == null) continue;
            if (type.equals(Action.MNEMONIC_KEY)) {
                Integer n = (a == null) ? null : (Integer)(Integer)a.getValue(type);
                setMnemonic(n == null ? '\000' : n.intValue());
            } else if (type.equals(Action.NAME)) {
                Boolean hide = (Boolean)(Boolean)getClientProperty("hideActionText");
                setText(a != null && hide != Boolean.TRUE ? (String)(String)a.getValue(Action.NAME) : null);
            } else if (type.equals(Action.SHORT_DESCRIPTION)) {
                setToolTipText(a != null ? (String)(String)a.getValue(type) : null);
            } else if (type.equals(Action.SMALL_ICON)) {
                setIcon(a != null ? (Icon)(Icon)a.getValue(type) : null);
            } else if (type.equals(Action.ACTION_COMMAND_KEY)) {
                setActionCommand(a != null ? (String)(String)a.getValue(type) : null);
            } else if (type.equals("enabled")) {
                setEnabled(a != null ? a.isEnabled() : true);
            }
        }
    }
    
    protected PropertyChangeListener createActionPropertyChangeListener(Action a) {
        return new AbstractButton$ButtonActionPropertyChangeListener(this, a);
    }
    {
    }
    
    public boolean isBorderPainted() {
        return paintBorder;
    }
    
    public void setBorderPainted(boolean b) {
        boolean oldValue = paintBorder;
        paintBorder = b;
        borderPaintedSet = true;
        firePropertyChange(BORDER_PAINTED_CHANGED_PROPERTY, oldValue, paintBorder);
        if (b != oldValue) {
            revalidate();
            repaint();
        }
    }
    
    protected void paintBorder(Graphics g) {
        if (isBorderPainted()) {
            super.paintBorder(g);
        }
    }
    
    public boolean isFocusPainted() {
        return paintFocus;
    }
    
    public void setFocusPainted(boolean b) {
        boolean oldValue = paintFocus;
        paintFocus = b;
        firePropertyChange(FOCUS_PAINTED_CHANGED_PROPERTY, oldValue, paintFocus);
        if (b != oldValue && isFocusOwner()) {
            revalidate();
            repaint();
        }
    }
    
    public boolean isContentAreaFilled() {
        return contentAreaFilled;
    }
    
    public void setContentAreaFilled(boolean b) {
        boolean oldValue = contentAreaFilled;
        contentAreaFilled = b;
        contentAreaFilledSet = true;
        firePropertyChange(CONTENT_AREA_FILLED_CHANGED_PROPERTY, oldValue, contentAreaFilled);
        if (b != oldValue) {
            repaint();
        }
    }
    
    public boolean isRolloverEnabled() {
        return rolloverEnabled;
    }
    
    public void setRolloverEnabled(boolean b) {
        boolean oldValue = rolloverEnabled;
        rolloverEnabled = b;
        rolloverEnabledSet = true;
        firePropertyChange(ROLLOVER_ENABLED_CHANGED_PROPERTY, oldValue, rolloverEnabled);
        if (b != oldValue) {
            repaint();
        }
    }
    
    public int getMnemonic() {
        return mnemonic;
    }
    
    public void setMnemonic(int mnemonic) {
        int oldValue = getMnemonic();
        model.setMnemonic(mnemonic);
        updateMnemonicProperties();
    }
    
    public void setMnemonic(char mnemonic) {
        int vk = (int)mnemonic;
        if (vk >= 'a' && vk <= 'z') vk -= ('a' - 'A');
        setMnemonic(vk);
    }
    
    public void setDisplayedMnemonicIndex(int index) throws IllegalArgumentException {
        int oldValue = mnemonicIndex;
        if (index == -1) {
            mnemonicIndex = -1;
        } else {
            String text = getText();
            int textLength = (text == null) ? 0 : text.length();
            if (index < -1 || index >= textLength) {
                throw new IllegalArgumentException("index == " + index);
            }
        }
        mnemonicIndex = index;
        firePropertyChange("displayedMnemonicIndex", oldValue, index);
        if (index != oldValue) {
            revalidate();
            repaint();
        }
    }
    
    public int getDisplayedMnemonicIndex() {
        return mnemonicIndex;
    }
    
    private void updateDisplayedMnemonicIndex(String text, int mnemonic) {
        setDisplayedMnemonicIndex(SwingUtilities.findDisplayedMnemonicIndex(text, mnemonic));
    }
    
    private void updateMnemonicProperties() {
        int newMnemonic = model.getMnemonic();
        if (mnemonic != newMnemonic) {
            int oldValue = mnemonic;
            mnemonic = newMnemonic;
            firePropertyChange(MNEMONIC_CHANGED_PROPERTY, oldValue, mnemonic);
            updateDisplayedMnemonicIndex(getText(), mnemonic);
            revalidate();
            repaint();
        }
    }
    
    public void setMultiClickThreshhold(long threshhold) {
        if (threshhold < 0) {
            throw new IllegalArgumentException("threshhold must be >= 0");
        }
        this.multiClickThreshhold = threshhold;
    }
    
    public long getMultiClickThreshhold() {
        return multiClickThreshhold;
    }
    
    public ButtonModel getModel() {
        return model;
    }
    
    public void setModel(ButtonModel newModel) {
        ButtonModel oldModel = getModel();
        if (oldModel != null) {
            oldModel.removeChangeListener(changeListener);
            oldModel.removeActionListener(actionListener);
            oldModel.removeItemListener(itemListener);
            changeListener = null;
            actionListener = null;
            itemListener = null;
        }
        model = newModel;
        if (newModel != null) {
            changeListener = createChangeListener();
            actionListener = createActionListener();
            itemListener = createItemListener();
            newModel.addChangeListener(changeListener);
            newModel.addActionListener(actionListener);
            newModel.addItemListener(itemListener);
            updateMnemonicProperties();
        } else {
            mnemonic = '\000';
        }
        updateDisplayedMnemonicIndex(getText(), mnemonic);
        firePropertyChange(MODEL_CHANGED_PROPERTY, oldModel, newModel);
        if (newModel != oldModel) {
            revalidate();
            repaint();
        }
    }
    
    public ButtonUI getUI() {
        return (ButtonUI)(ButtonUI)ui;
    }
    
    public void setUI(ButtonUI ui) {
        super.setUI(ui);
        if (disabledIcon instanceof UIResource) {
            setDisabledIcon(null);
        }
        if (disabledSelectedIcon instanceof UIResource) {
            setDisabledSelectedIcon(null);
        }
    }
    
    public void updateUI() {
    }
    
    protected void addImpl(Component comp, Object constraints, int index) {
        if (!setLayout) {
            setLayout(new OverlayLayout(this));
        }
        super.addImpl(comp, constraints, index);
    }
    
    public void setLayout(LayoutManager mgr) {
        setLayout = true;
        super.setLayout(mgr);
    }
    
    public void addChangeListener(ChangeListener l) {
        listenerList.add(ChangeListener.class, l);
    }
    
    public void removeChangeListener(ChangeListener l) {
        listenerList.remove(ChangeListener.class, l);
    }
    
    public ChangeListener[] getChangeListeners() {
        return (ChangeListener[])((ChangeListener[])listenerList.getListeners(ChangeListener.class));
    }
    
    protected void fireStateChanged() {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ChangeListener.class) {
                if (changeEvent == null) changeEvent = new ChangeEvent(this);
                ((ChangeListener)(ChangeListener)listeners[i + 1]).stateChanged(changeEvent);
            }
        }
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
        return (ActionListener[])((ActionListener[])listenerList.getListeners(ActionListener.class));
    }
    
    protected ChangeListener createChangeListener() {
        return getHandler();
    }
    {
    }
    
    protected void fireActionPerformed(ActionEvent event) {
        Object[] listeners = listenerList.getListenerList();
        ActionEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ActionListener.class) {
                if (e == null) {
                    String actionCommand = event.getActionCommand();
                    if (actionCommand == null) {
                        actionCommand = getActionCommand();
                    }
                    e = new ActionEvent(this, ActionEvent.ACTION_PERFORMED, actionCommand, event.getWhen(), event.getModifiers());
                }
                ((ActionListener)(ActionListener)listeners[i + 1]).actionPerformed(e);
            }
        }
    }
    
    protected void fireItemStateChanged(ItemEvent event) {
        Object[] listeners = listenerList.getListenerList();
        ItemEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ItemListener.class) {
                if (e == null) {
                    e = new ItemEvent(this, ItemEvent.ITEM_STATE_CHANGED, this, event.getStateChange());
                }
                ((ItemListener)(ItemListener)listeners[i + 1]).itemStateChanged(e);
            }
        }
        if (accessibleContext != null) {
            if (event.getStateChange() == ItemEvent.SELECTED) {
                accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.SELECTED);
                accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VALUE_PROPERTY, new Integer(0), new Integer(1));
            } else {
                accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.SELECTED, null);
                accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VALUE_PROPERTY, new Integer(1), new Integer(0));
            }
        }
    }
    
    protected ActionListener createActionListener() {
        return getHandler();
    }
    
    protected ItemListener createItemListener() {
        return getHandler();
    }
    
    public void setEnabled(boolean b) {
        if (!b && model.isRollover()) {
            model.setRollover(false);
        }
        super.setEnabled(b);
        model.setEnabled(b);
    }
    
    
    public String getLabel() {
        return getText();
    }
    
    
    public void setLabel(String label) {
        setText(label);
    }
    
    public void addItemListener(ItemListener l) {
        listenerList.add(ItemListener.class, l);
    }
    
    public void removeItemListener(ItemListener l) {
        listenerList.remove(ItemListener.class, l);
    }
    
    public ItemListener[] getItemListeners() {
        return (ItemListener[])(ItemListener[])listenerList.getListeners(ItemListener.class);
    }
    
    public Object[] getSelectedObjects() {
        if (isSelected() == false) {
            return null;
        }
        Object[] selectedObjects = new Object[1];
        selectedObjects[0] = getText();
        return selectedObjects;
    }
    
    protected void init(String text, Icon icon) {
        if (text != null) {
            setText(text);
        }
        if (icon != null) {
            setIcon(icon);
        }
        updateUI();
        setAlignmentX(LEFT_ALIGNMENT);
        setAlignmentY(CENTER_ALIGNMENT);
    }
    
    public boolean imageUpdate(Image img, int infoflags, int x, int y, int w, int h) {
        Icon iconDisplayed = getIcon();
        if (iconDisplayed == null) {
            return false;
        }
        if (!model.isEnabled()) {
            if (model.isSelected()) {
                iconDisplayed = getDisabledSelectedIcon();
            } else {
                iconDisplayed = getDisabledIcon();
            }
        } else if (model.isPressed() && model.isArmed()) {
            iconDisplayed = getPressedIcon();
        } else if (isRolloverEnabled() && model.isRollover()) {
            if (model.isSelected()) {
                iconDisplayed = getRolloverSelectedIcon();
            } else {
                iconDisplayed = getRolloverIcon();
            }
        } else if (model.isSelected()) {
            iconDisplayed = getSelectedIcon();
        }
        if (!SwingUtilities.doesIconReferenceImage(iconDisplayed, img)) {
            return false;
        }
        return super.imageUpdate(img, infoflags, x, y, w, h);
    }
    
    void setUIProperty(String propertyName, Object value) {
        if (propertyName == "borderPainted") {
            if (!borderPaintedSet) {
                setBorderPainted(((Boolean)(Boolean)value).booleanValue());
                borderPaintedSet = false;
            }
        } else if (propertyName == "rolloverEnabled") {
            if (!rolloverEnabledSet) {
                setRolloverEnabled(((Boolean)(Boolean)value).booleanValue());
                rolloverEnabledSet = false;
            }
        } else if (propertyName == "iconTextGap") {
            if (!iconTextGapSet) {
                setIconTextGap(((Number)(Number)value).intValue());
                iconTextGapSet = false;
            }
        } else if (propertyName == "contentAreaFilled") {
            if (!contentAreaFilledSet) {
                setContentAreaFilled(((Boolean)(Boolean)value).booleanValue());
                contentAreaFilledSet = false;
            }
        } else {
            super.setUIProperty(propertyName, value);
        }
    }
    
    protected String paramString() {
        String defaultIconString = ((defaultIcon != null) && (defaultIcon != this) ? defaultIcon.toString() : "");
        String pressedIconString = ((pressedIcon != null) && (pressedIcon != this) ? pressedIcon.toString() : "");
        String disabledIconString = ((disabledIcon != null) && (disabledIcon != this) ? disabledIcon.toString() : "");
        String selectedIconString = ((selectedIcon != null) && (selectedIcon != this) ? selectedIcon.toString() : "");
        String disabledSelectedIconString = ((disabledSelectedIcon != null) && (disabledSelectedIcon != this) ? disabledSelectedIcon.toString() : "");
        String rolloverIconString = ((rolloverIcon != null) && (rolloverIcon != this) ? rolloverIcon.toString() : "");
        String rolloverSelectedIconString = ((rolloverSelectedIcon != null) && (rolloverSelectedIcon != this) ? rolloverSelectedIcon.toString() : "");
        String paintBorderString = (paintBorder ? "true" : "false");
        String paintFocusString = (paintFocus ? "true" : "false");
        String rolloverEnabledString = (rolloverEnabled ? "true" : "false");
        return super.paramString() + ",defaultIcon=" + defaultIconString + ",disabledIcon=" + disabledIconString + ",disabledSelectedIcon=" + disabledSelectedIconString + ",margin=" + margin + ",paintBorder=" + paintBorderString + ",paintFocus=" + paintFocusString + ",pressedIcon=" + pressedIconString + ",rolloverEnabled=" + rolloverEnabledString + ",rolloverIcon=" + rolloverIconString + ",rolloverSelectedIcon=" + rolloverSelectedIconString + ",selectedIcon=" + selectedIconString + ",text=" + text;
    }
    
    private AbstractButton$Handler getHandler() {
        if (handler == null) {
            handler = new AbstractButton$Handler(this);
        }
        return handler;
    }
    {
    }
    {
    }
}
