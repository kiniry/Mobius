package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.dnd.*;
import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.event.*;
import javax.swing.Timer;

class BasicDropTargetListener implements DropTargetListener, UIResource, ActionListener {
    
    protected BasicDropTargetListener() {
        
    }
    
    protected void saveComponentState(JComponent c) {
    }
    
    protected void restoreComponentState(JComponent c) {
    }
    
    protected void restoreComponentStateForDrop(JComponent c) {
    }
    
    protected void updateInsertionLocation(JComponent c, Point p) {
    }
    private static final int AUTOSCROLL_INSET = 10;
    
    void updateAutoscrollRegion(JComponent c) {
        Rectangle visible = c.getVisibleRect();
        outer.reshape(visible.x, visible.y, visible.width, visible.height);
        Insets i = new Insets(0, 0, 0, 0);
        if (c instanceof Scrollable) {
            int minSize = 2 * AUTOSCROLL_INSET;
            if (visible.width >= minSize) {
                i.left = i.right = AUTOSCROLL_INSET;
            }
            if (visible.height >= minSize) {
                i.top = i.bottom = AUTOSCROLL_INSET;
            }
        }
        inner.reshape(visible.x + i.left, visible.y + i.top, visible.width - (i.left + i.right), visible.height - (i.top + i.bottom));
    }
    
    void autoscroll(JComponent c, Point pos) {
        if (c instanceof Scrollable) {
            Scrollable s = (Scrollable)(Scrollable)c;
            if (pos.y < inner.y) {
                int dy = s.getScrollableUnitIncrement(outer, SwingConstants.VERTICAL, -1);
                Rectangle r = new Rectangle(inner.x, outer.y - dy, inner.width, dy);
                c.scrollRectToVisible(r);
            } else if (pos.y > (inner.y + inner.height)) {
                int dy = s.getScrollableUnitIncrement(outer, SwingConstants.VERTICAL, 1);
                Rectangle r = new Rectangle(inner.x, outer.y + outer.height, inner.width, dy);
                c.scrollRectToVisible(r);
            }
            if (pos.x < inner.x) {
                int dx = s.getScrollableUnitIncrement(outer, SwingConstants.HORIZONTAL, -1);
                Rectangle r = new Rectangle(outer.x - dx, inner.y, dx, inner.height);
                c.scrollRectToVisible(r);
            } else if (pos.x > (inner.x + inner.width)) {
                int dx = s.getScrollableUnitIncrement(outer, SwingConstants.HORIZONTAL, 1);
                Rectangle r = new Rectangle(outer.x + outer.width, inner.y, dx, inner.height);
                c.scrollRectToVisible(r);
            }
        }
    }
    
    private void initPropertiesIfNecessary() {
        if (timer == null) {
            Toolkit t = Toolkit.getDefaultToolkit();
            Integer initial = new Integer(100);
            Integer interval = new Integer(100);
            try {
                initial = (Integer)(Integer)t.getDesktopProperty("DnD.Autoscroll.initialDelay");
            } catch (Exception e) {
            }
            try {
                interval = (Integer)(Integer)t.getDesktopProperty("DnD.Autoscroll.interval");
            } catch (Exception e) {
            }
            timer = new Timer(interval.intValue(), this);
            timer.setCoalesce(true);
            timer.setInitialDelay(initial.intValue());
            try {
                hysteresis = ((Integer)(Integer)t.getDesktopProperty("DnD.Autoscroll.cursorHysteresis")).intValue();
            } catch (Exception e) {
            }
        }
    }
    
    static JComponent getComponent(DropTargetEvent e) {
        DropTargetContext context = e.getDropTargetContext();
        return (JComponent)(JComponent)context.getComponent();
    }
    
    public synchronized void actionPerformed(ActionEvent e) {
        updateAutoscrollRegion(component);
        if (outer.contains(lastPosition) && !inner.contains(lastPosition)) {
            autoscroll(component, lastPosition);
        }
    }
    
    public void dragEnter(DropTargetDragEvent e) {
        component = getComponent(e);
        TransferHandler th = component.getTransferHandler();
        canImport = th.canImport(component, e.getCurrentDataFlavors());
        if (canImport) {
            saveComponentState(component);
            lastPosition = e.getLocation();
            updateAutoscrollRegion(component);
            initPropertiesIfNecessary();
        }
    }
    
    public void dragOver(DropTargetDragEvent e) {
        if (canImport) {
            Point p = e.getLocation();
            updateInsertionLocation(component, p);
            synchronized (this) {
                if (Math.abs(p.x - lastPosition.x) > hysteresis || Math.abs(p.y - lastPosition.y) > hysteresis) {
                    if (timer.isRunning()) timer.stop();
                } else {
                    if (!timer.isRunning()) timer.start();
                }
                lastPosition = p;
            }
        }
    }
    
    public void dragExit(DropTargetEvent e) {
        if (canImport) {
            restoreComponentState(component);
        }
        cleanup();
    }
    
    public void drop(DropTargetDropEvent e) {
        if (canImport) {
            restoreComponentStateForDrop(component);
        }
        cleanup();
    }
    
    public void dropActionChanged(DropTargetDragEvent e) {
    }
    
    private void cleanup() {
        if (timer != null) {
            timer.stop();
        }
        component = null;
        lastPosition = null;
    }
    private Timer timer;
    private Point lastPosition;
    private Rectangle outer = new Rectangle();
    private Rectangle inner = new Rectangle();
    private int hysteresis = 10;
    private boolean canImport;
    private JComponent component;
}
