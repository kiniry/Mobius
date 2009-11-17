package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.plaf.RootPaneUI;
import javax.swing.border.*;

public class JRootPane extends JComponent implements Accessible {
    private static final String uiClassID = "RootPaneUI";
    public static final int NONE = 0;
    public static final int FRAME = 1;
    public static final int PLAIN_DIALOG = 2;
    public static final int INFORMATION_DIALOG = 3;
    public static final int ERROR_DIALOG = 4;
    public static final int COLOR_CHOOSER_DIALOG = 5;
    public static final int FILE_CHOOSER_DIALOG = 6;
    public static final int QUESTION_DIALOG = 7;
    public static final int WARNING_DIALOG = 8;
    private Component mostRecentFocusOwner;
    private int windowDecorationStyle;
    protected JMenuBar menuBar;
    protected Container contentPane;
    protected JLayeredPane layeredPane;
    protected Component glassPane;
    protected JButton defaultButton;
    
    protected JRootPane$DefaultAction defaultPressAction;
    
    protected JRootPane$DefaultAction defaultReleaseAction;
    
    public JRootPane() {
        
        setGlassPane(createGlassPane());
        setLayeredPane(createLayeredPane());
        setContentPane(createContentPane());
        setLayout(createRootLayout());
        setDoubleBuffered(true);
        updateUI();
    }
    
    public int getWindowDecorationStyle() {
        return windowDecorationStyle;
    }
    
    public void setWindowDecorationStyle(int windowDecorationStyle) {
        if (windowDecorationStyle < 0 || windowDecorationStyle > WARNING_DIALOG) {
            throw new IllegalArgumentException("Invalid decoration style");
        }
        int oldWindowDecorationStyle = getWindowDecorationStyle();
        this.windowDecorationStyle = windowDecorationStyle;
        firePropertyChange("windowDecorationStyle", oldWindowDecorationStyle, windowDecorationStyle);
    }
    
    public RootPaneUI getUI() {
        return (RootPaneUI)(RootPaneUI)ui;
    }
    
    public void setUI(RootPaneUI ui) {
        super.setUI(ui);
    }
    
    public void updateUI() {
        setUI((RootPaneUI)(RootPaneUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    protected JLayeredPane createLayeredPane() {
        JLayeredPane p = new JLayeredPane();
        p.setName(this.getName() + ".layeredPane");
        return p;
    }
    
    protected Container createContentPane() {
        JComponent c = new JPanel();
        c.setName(this.getName() + ".contentPane");
        c.setLayout(new JRootPane$1(this));
        return c;
    }
    
    protected Component createGlassPane() {
        JComponent c = new JPanel();
        c.setName(this.getName() + ".glassPane");
        c.setVisible(false);
        ((JPanel)(JPanel)c).setOpaque(false);
        return c;
    }
    
    protected LayoutManager createRootLayout() {
        return new JRootPane$RootLayout(this);
    }
    
    public void setJMenuBar(JMenuBar menu) {
        if (menuBar != null && menuBar.getParent() == layeredPane) layeredPane.remove(menuBar);
        menuBar = menu;
        if (menuBar != null) layeredPane.add(menuBar, JLayeredPane.FRAME_CONTENT_LAYER);
    }
    
    
    public void setMenuBar(JMenuBar menu) {
        if (menuBar != null && menuBar.getParent() == layeredPane) layeredPane.remove(menuBar);
        menuBar = menu;
        if (menuBar != null) layeredPane.add(menuBar, JLayeredPane.FRAME_CONTENT_LAYER);
    }
    
    public JMenuBar getJMenuBar() {
        return menuBar;
    }
    
    
    public JMenuBar getMenuBar() {
        return menuBar;
    }
    
    public void setContentPane(Container content) {
        if (content == null) throw new IllegalComponentStateException("contentPane cannot be set to null.");
        if (contentPane != null && contentPane.getParent() == layeredPane) layeredPane.remove(contentPane);
        contentPane = content;
        layeredPane.add(contentPane, JLayeredPane.FRAME_CONTENT_LAYER);
    }
    
    public Container getContentPane() {
        return contentPane;
    }
    
    public void setLayeredPane(JLayeredPane layered) {
        if (layered == null) throw new IllegalComponentStateException("layeredPane cannot be set to null.");
        if (layeredPane != null && layeredPane.getParent() == this) this.remove(layeredPane);
        layeredPane = layered;
        this.add(layeredPane, -1);
    }
    
    public JLayeredPane getLayeredPane() {
        return layeredPane;
    }
    
    public void setGlassPane(Component glass) {
        if (glass == null) {
            throw new NullPointerException("glassPane cannot be set to null.");
        }
        boolean visible = false;
        if (glassPane != null && glassPane.getParent() == this) {
            this.remove(glassPane);
            visible = glassPane.isVisible();
        }
        glass.setVisible(visible);
        glassPane = glass;
        this.add(glassPane, 0);
        if (visible) {
            repaint();
        }
    }
    
    public Component getGlassPane() {
        return glassPane;
    }
    
    public boolean isValidateRoot() {
        return true;
    }
    
    public boolean isOptimizedDrawingEnabled() {
        return !glassPane.isVisible();
    }
    
    public void addNotify() {
        SystemEventQueueUtilities.addRunnableCanvas(this);
        super.addNotify();
        enableEvents(AWTEvent.KEY_EVENT_MASK);
    }
    
    public void removeNotify() {
        SystemEventQueueUtilities.removeRunnableCanvas(this);
        super.removeNotify();
    }
    
    public void setDefaultButton(JButton defaultButton) {
        JButton oldDefault = this.defaultButton;
        if (oldDefault != defaultButton) {
            this.defaultButton = defaultButton;
            if (oldDefault != null) {
                oldDefault.repaint();
            }
            if (defaultButton != null) {
                defaultButton.repaint();
            }
        }
        firePropertyChange("defaultButton", oldDefault, defaultButton);
    }
    
    public JButton getDefaultButton() {
        return defaultButton;
    }
    {
    }
    
    protected void addImpl(Component comp, Object constraints, int index) {
        super.addImpl(comp, constraints, index);
        if (glassPane != null && glassPane.getParent() == this && getComponent(0) != glassPane) {
            add(glassPane, 0);
        }
    }
    {
    }
    
    void setMostRecentFocusOwner(Component focusOwner) {
        mostRecentFocusOwner = focusOwner;
    }
    
    Component getMostRecentFocusOwner() {
        return mostRecentFocusOwner;
    }
    
    protected String paramString() {
        return super.paramString();
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JRootPane$AccessibleJRootPane(this);
        }
        return accessibleContext;
    }
    {
    }
}
