package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.applet.Applet;
import javax.accessibility.*;

public class JApplet extends Applet implements Accessible, RootPaneContainer {
    protected JRootPane rootPane;
    protected boolean rootPaneCheckingEnabled = false;
    
    public JApplet() throws HeadlessException {
        
        TimerQueue q = TimerQueue.sharedInstance();
        if (q != null) {
            synchronized (q) {
                if (!q.running) q.start();
            }
        }
        setForeground(Color.black);
        setBackground(Color.white);
        setLocale(JComponent.getDefaultLocale());
        setLayout(new BorderLayout());
        setRootPane(createRootPane());
        setRootPaneCheckingEnabled(true);
        setFocusTraversalPolicyProvider(true);
        sun.awt.SunToolkit.checkAndSetPolicy(this, true);
        enableEvents(AWTEvent.KEY_EVENT_MASK);
    }
    
    protected JRootPane createRootPane() {
        JRootPane rp = new JRootPane();
        rp.setOpaque(true);
        return rp;
    }
    
    public void update(Graphics g) {
        paint(g);
    }
    
    public void setJMenuBar(JMenuBar menuBar) {
        getRootPane().setMenuBar(menuBar);
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
    
    protected String paramString() {
        String rootPaneString = (rootPane != null ? rootPane.toString() : "");
        String rootPaneCheckingEnabledString = (rootPaneCheckingEnabled ? "true" : "false");
        return super.paramString() + ",rootPane=" + rootPaneString + ",rootPaneCheckingEnabled=" + rootPaneCheckingEnabledString;
    }
    protected AccessibleContext accessibleContext = null;
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JApplet$AccessibleJApplet(this);
        }
        return accessibleContext;
    }
    {
    }
}
