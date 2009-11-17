package java.awt.dnd;

import java.awt.Component;
import java.awt.Dimension;
import java.awt.Insets;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.Timer;

public class DropTarget$DropTargetAutoScroller implements ActionListener {
    
    protected DropTarget$DropTargetAutoScroller(Component c, Point p) {
        
        component = c;
        autoScroll = (Autoscroll)(Autoscroll)component;
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
        locn = p;
        prev = p;
        try {
            hysteresis = ((Integer)(Integer)t.getDesktopProperty("DnD.Autoscroll.cursorHysteresis")).intValue();
        } catch (Exception e) {
        }
        timer.start();
    }
    
    private void updateRegion() {
        Insets i = autoScroll.getAutoscrollInsets();
        Dimension size = component.getSize();
        if (size.width != outer.width || size.height != outer.height) outer.reshape(0, 0, size.width, size.height);
        if (inner.x != i.left || inner.y != i.top) inner.setLocation(i.left, i.top);
        int newWidth = size.width - (i.left + i.right);
        int newHeight = size.height - (i.top + i.bottom);
        if (newWidth != inner.width || newHeight != inner.height) inner.setSize(newWidth, newHeight);
    }
    
    protected synchronized void updateLocation(Point newLocn) {
        prev = locn;
        locn = newLocn;
        if (Math.abs(locn.x - prev.x) > hysteresis || Math.abs(locn.y - prev.y) > hysteresis) {
            if (timer.isRunning()) timer.stop();
        } else {
            if (!timer.isRunning()) timer.start();
        }
    }
    
    protected void stop() {
        timer.stop();
    }
    
    public synchronized void actionPerformed(ActionEvent e) {
        updateRegion();
        if (outer.contains(locn) && !inner.contains(locn)) autoScroll.autoscroll(locn);
    }
    private Component component;
    private Autoscroll autoScroll;
    private Timer timer;
    private Point locn;
    private Point prev;
    private Rectangle outer = new Rectangle();
    private Rectangle inner = new Rectangle();
    private int hysteresis = 10;
}
