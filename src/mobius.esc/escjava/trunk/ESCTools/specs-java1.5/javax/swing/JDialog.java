package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.accessibility.*;

public class JDialog extends Dialog implements WindowConstants, Accessible, RootPaneContainer {
    private static final Object defaultLookAndFeelDecoratedKey = new StringBuffer("JDialog.defaultLookAndFeelDecorated");
    private int defaultCloseOperation = HIDE_ON_CLOSE;
    protected JRootPane rootPane;
    protected boolean rootPaneCheckingEnabled = false;
    
    public JDialog() throws HeadlessException {
        this((Frame)null, false);
    }
    
    public JDialog(Frame owner) throws HeadlessException {
        this(owner, false);
    }
    
    public JDialog(Frame owner, boolean modal) throws HeadlessException {
        this(owner, null, modal);
    }
    
    public JDialog(Frame owner, String title) throws HeadlessException {
        this(owner, title, false);
    }
    
    public JDialog(Frame owner, String title, boolean modal) throws HeadlessException {
        super(owner == null ? SwingUtilities.getSharedOwnerFrame() : owner, title, modal);
        if (owner == null) {
            WindowListener ownerShutdownListener = (WindowListener)SwingUtilities.getSharedOwnerFrameShutdownListener();
            addWindowListener(ownerShutdownListener);
        }
        dialogInit();
    }
    
    public JDialog(Frame owner, String title, boolean modal, GraphicsConfiguration gc) {
        super(owner == null ? SwingUtilities.getSharedOwnerFrame() : owner, title, modal, gc);
        if (owner == null) {
            WindowListener ownerShutdownListener = (WindowListener)SwingUtilities.getSharedOwnerFrameShutdownListener();
            addWindowListener(ownerShutdownListener);
        }
        dialogInit();
    }
    
    public JDialog(Dialog owner) throws HeadlessException {
        this(owner, false);
    }
    
    public JDialog(Dialog owner, boolean modal) throws HeadlessException {
        this(owner, null, modal);
    }
    
    public JDialog(Dialog owner, String title) throws HeadlessException {
        this(owner, title, false);
    }
    
    public JDialog(Dialog owner, String title, boolean modal) throws HeadlessException {
        super(owner, title, modal);
        dialogInit();
    }
    
    public JDialog(Dialog owner, String title, boolean modal, GraphicsConfiguration gc) throws HeadlessException {
        super(owner, title, modal, gc);
        dialogInit();
    }
    
    protected void dialogInit() {
        enableEvents(AWTEvent.KEY_EVENT_MASK | AWTEvent.WINDOW_EVENT_MASK);
        setLocale(JComponent.getDefaultLocale());
        setRootPane(createRootPane());
        setRootPaneCheckingEnabled(true);
        if (JDialog.isDefaultLookAndFeelDecorated()) {
            boolean supportsWindowDecorations = UIManager.getLookAndFeel().getSupportsWindowDecorations();
            if (supportsWindowDecorations) {
                setUndecorated(true);
                getRootPane().setWindowDecorationStyle(JRootPane.PLAIN_DIALOG);
            }
        }
        sun.awt.SunToolkit.checkAndSetPolicy(this, true);
    }
    
    protected JRootPane createRootPane() {
        JRootPane rp = new JRootPane();
        rp.setOpaque(true);
        return rp;
    }
    
    protected void processWindowEvent(WindowEvent e) {
        super.processWindowEvent(e);
        if (e.getID() == WindowEvent.WINDOW_CLOSING) {
            switch (defaultCloseOperation) {
            case HIDE_ON_CLOSE: 
                setVisible(false);
                break;
            
            case DISPOSE_ON_CLOSE: 
                setVisible(false);
                dispose();
                break;
            
            case DO_NOTHING_ON_CLOSE: 
            
            default: 
                break;
            
            }
        }
    }
    
    public void setDefaultCloseOperation(int operation) {
        this.defaultCloseOperation = operation;
    }
    
    public int getDefaultCloseOperation() {
        return defaultCloseOperation;
    }
    
    public void update(Graphics g) {
        paint(g);
    }
    
    public void setJMenuBar(JMenuBar menu) {
        getRootPane().setMenuBar(menu);
    }
    
    public JMenuBar getJMenuBar() {
        return getRootPane().getMenuBar();
    }
    
    protected boolean isRootPaneCheckingEnabled() {
        return rootPaneCheckingEnabled;
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
    
    public static void setDefaultLookAndFeelDecorated(boolean defaultLookAndFeelDecorated) {
        if (defaultLookAndFeelDecorated) {
            SwingUtilities.appContextPut(defaultLookAndFeelDecoratedKey, Boolean.TRUE);
        } else {
            SwingUtilities.appContextPut(defaultLookAndFeelDecoratedKey, Boolean.FALSE);
        }
    }
    
    public static boolean isDefaultLookAndFeelDecorated() {
        Boolean defaultLookAndFeelDecorated = (Boolean)(Boolean)SwingUtilities.appContextGet(defaultLookAndFeelDecoratedKey);
        if (defaultLookAndFeelDecorated == null) {
            defaultLookAndFeelDecorated = Boolean.FALSE;
        }
        return defaultLookAndFeelDecorated.booleanValue();
    }
    
    protected String paramString() {
        String defaultCloseOperationString;
        if (defaultCloseOperation == HIDE_ON_CLOSE) {
            defaultCloseOperationString = "HIDE_ON_CLOSE";
        } else if (defaultCloseOperation == DISPOSE_ON_CLOSE) {
            defaultCloseOperationString = "DISPOSE_ON_CLOSE";
        } else if (defaultCloseOperation == DO_NOTHING_ON_CLOSE) {
            defaultCloseOperationString = "DO_NOTHING_ON_CLOSE";
        } else defaultCloseOperationString = "";
        String rootPaneString = (rootPane != null ? rootPane.toString() : "");
        String rootPaneCheckingEnabledString = (rootPaneCheckingEnabled ? "true" : "false");
        return super.paramString() + ",defaultCloseOperation=" + defaultCloseOperationString + ",rootPane=" + rootPaneString + ",rootPaneCheckingEnabled=" + rootPaneCheckingEnabledString;
    }
    protected AccessibleContext accessibleContext = null;
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JDialog$AccessibleJDialog(this);
        }
        return accessibleContext;
    }
    {
    }
}
