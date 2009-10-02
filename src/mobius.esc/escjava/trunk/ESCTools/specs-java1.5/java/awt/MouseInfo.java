package java.awt;

import sun.security.util.SecurityConstants;

public class MouseInfo {
    /*synthetic*/ static final boolean $assertionsDisabled = !MouseInfo.class.desiredAssertionStatus();
    
    private MouseInfo() {
        
    }
    
    public static PointerInfo getPointerInfo() throws HeadlessException {
        if (GraphicsEnvironment.isHeadless()) {
            throw new HeadlessException();
        }
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkPermission(SecurityConstants.WATCH_MOUSE_PERMISSION);
        }
        Point point = new Point(0, 0);
        int deviceNum = Toolkit.getDefaultToolkit().getMouseInfoPeer().fillPointWithCoords(point);
        GraphicsDevice[] gds = GraphicsEnvironment.getLocalGraphicsEnvironment().getScreenDevices();
        PointerInfo retval = null;
        if (areScreenDevicesIndependent(gds)) {
            retval = new PointerInfo(gds[deviceNum], point);
        } else {
            for (int i = 0; i < gds.length; i++) {
                GraphicsConfiguration gc = gds[i].getDefaultConfiguration();
                Rectangle bounds = gc.getBounds();
                if (bounds.contains(point)) {
                    retval = new PointerInfo(gds[i], point);
                }
            }
        }
        return retval;
    }
    
    private static boolean areScreenDevicesIndependent(GraphicsDevice[] gds) {
        for (int i = 0; i < gds.length; i++) {
            Rectangle bounds = gds[i].getDefaultConfiguration().getBounds();
            if (bounds.x != 0 || bounds.y != 0) {
                return false;
            }
        }
        return true;
    }
    
    public static int getNumberOfButtons() throws HeadlessException {
        if (GraphicsEnvironment.isHeadless()) {
            throw new HeadlessException();
        }
        Object prop = Toolkit.getDefaultToolkit().getDesktopProperty("awt.mouse.numButtons");
        if (prop instanceof Integer) {
            return ((Integer)(Integer)prop).intValue();
        }
        if (!$assertionsDisabled) throw new AssertionError("awt.mouse.numButtons is not an integer property");
        return 0;
    }
}
