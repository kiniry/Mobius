package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.accessibility.*;

public class JWindow extends Window implements Accessible, RootPaneContainer {
    protected JRootPane rootPane;
    protected boolean rootPaneCheckingEnabled = false;
    
    public JWindow() {
        this((Frame)null);
    }
    
    public JWindow(GraphicsConfiguration gc) {
        this(null, gc);
        super.setFocusableWindowState(false);
    }
    
    public JWindow(Frame owner) {
        super(owner == null ? SwingUtilities.getSharedOwnerFrame() : owner);
        if (owner == null) {
            WindowListener ownerShutdownListener = (WindowListener)SwingUtilities.getSharedOwnerFrameShutdownListener();
            addWindowListener(ownerShutdownListener);
        }
        windowInit();
    }
    
    public JWindow(Window owner) {
        super(owner == null ? (Window)SwingUtilities.getSharedOwnerFrame() : owner);
        if (owner == null) {
            WindowListener ownerShutdownListener = (WindowListener)SwingUtilities.getSharedOwnerFrameShutdownListener();
            addWindowListener(ownerShutdownListener);
        }
        windowInit();
    }
    
    public JWindow(Window owner, GraphicsConfiguration gc) {
        super(owner == null ? (Window)SwingUtilities.getSharedOwnerFrame() : owner, gc);
        if (owner == null) {
            WindowListener ownerShutdownListener = (WindowListener)SwingUtilities.getSharedOwnerFrameShutdownListener();
            addWindowListener(ownerShutdownListener);
        }
        windowInit();
    }
    
    protected void windowInit() {
        setLocale(JComponent.getDefaultLocale());
        setRootPane(createRootPane());
        setRootPaneCheckingEnabled(true);
        sun.awt.SunToolkit.checkAndSetPolicy(this, true);
    }
    
    protected JRootPane createRootPane() {
        JRootPane rp = new JRootPane();
        rp.setOpaque(true);
        return rp;
    }
    
    protected boolean isRootPaneCheckingEnabled() {
        return rootPaneCheckingEnabled;
    }
    
    public void update(Graphics g) {
        paint(g);
    }
    
    protected void setRootPaneCheckingEnabled(boolean enabled) {
        rootPaneCheckingEnabled = enabled;
    }
    
    protected void addImpl(Component comp, Object constraints, int index) {
        if (isRootPaneCheckingEnabled()) {
            getContentPane().add(comp, constraints, index);
        } else {
            super.addImpl(comp, constraints, index);
        }
    }
    
    public void remove(Component comp) {
        if (comp == rootPane) {
            super.remove(comp);
        } else {
            getContentPane().remove(comp);
        }
    }
    
    public void setLayout(LayoutManager manager) {
        if (isRootPaneCheckingEnabled()) {
            getContentPane().setLayout(manager);
        } else {
            super.setLayout(manager);
        }
    }
    
    public JRootPane getRootPane() {
        return rootPane;
    }
    
    protected void setRootPane(JRootPane root) {
        if (rootPane != null) {
            remove(rootPane);
        }
        rootPane = root;
        if (rootPane != null) {
            boolean checkingEnabled = isRootPaneCheckingEnabled();
            try {
                setRootPaneCheckingEnabled(false);
                add(rootPane, BorderLayout.CENTER);
            } finally {
                setRootPaneCheckingEnabled(checkingEnabled);
            }
        }
    }
    
    public Container getContentPane() {
        return getRootPane().getContentPane();
    }
    
    public void setContentPane(Container contentPane) {
        getRootPane().setContentPane(contentPane);
    }
    
    public JLayeredPane getLayeredPane() {
        return getRootPane().getLayeredPane();
    }
    
    public void setLayeredPane(JLayeredPane layeredPane) {
        getRootPane().setLayeredPane(layeredPane);
    }
    
    public Component getGlassPane() {
        return getRootPane().getGlassPane();
    }
    
    public void setGlassPane(Component glassPane) {
        getRootPane().setGlassPane(glassPane);
    }
    
    protected String paramString() {
        String rootPaneCheckingEnabledString = (rootPaneCheckingEnabled ? "true" : "false");
        return super.paramString() + ",rootPaneCheckingEnabled=" + rootPaneCheckingEnabledString;
    }
    protected AccessibleContext accessibleContext = null;
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JWindow$AccessibleJWindow(this);
        }
        return accessibleContext;
    }
    {
    }
}
