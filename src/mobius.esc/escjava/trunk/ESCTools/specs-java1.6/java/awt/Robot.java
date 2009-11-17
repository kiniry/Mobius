package java.awt;

import java.awt.peer.*;
import java.awt.image.*;
import java.awt.event.*;
import java.lang.reflect.InvocationTargetException;
import sun.awt.ComponentFactory;
import sun.awt.SunToolkit;
import sun.security.util.SecurityConstants;

public class Robot {
    private static final int MAX_DELAY = 60000;
    private RobotPeer peer;
    private boolean isAutoWaitForIdle = false;
    private int autoDelay = 0;
    private static final int LEGAL_BUTTON_MASK = InputEvent.BUTTON1_MASK | InputEvent.BUTTON2_MASK | InputEvent.BUTTON3_MASK;
    private DirectColorModel screenCapCM = null;
    
    public Robot() throws AWTException {
        
        if (GraphicsEnvironment.isHeadless()) {
            throw new AWTException("headless environment");
        }
        init(GraphicsEnvironment.getLocalGraphicsEnvironment().getDefaultScreenDevice());
    }
    
    public Robot(GraphicsDevice screen) throws AWTException {
        
        checkIsScreenDevice(screen);
        init(screen);
    }
    
    private void init(GraphicsDevice screen) throws AWTException {
        checkRobotAllowed();
        Toolkit toolkit = Toolkit.getDefaultToolkit();
        if (toolkit instanceof ComponentFactory) {
            peer = ((ComponentFactory)(ComponentFactory)toolkit).createRobot(this, screen);
        }
    }
    
    private void checkRobotAllowed() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkPermission(SecurityConstants.CREATE_ROBOT_PERMISSION);
        }
    }
    
    private void checkIsScreenDevice(GraphicsDevice device) {
        if (device == null || device.getType() != GraphicsDevice.TYPE_RASTER_SCREEN) {
            throw new IllegalArgumentException("not a valid screen device");
        }
    }
    
    public synchronized void mouseMove(int x, int y) {
        peer.mouseMove(x, y);
        afterEvent();
    }
    
    public synchronized void mousePress(int buttons) {
        checkButtonsArgument(buttons);
        peer.mousePress(buttons);
        afterEvent();
    }
    
    public synchronized void mouseRelease(int buttons) {
        checkButtonsArgument(buttons);
        peer.mouseRelease(buttons);
        afterEvent();
    }
    
    private void checkButtonsArgument(int buttons) {
        if ((buttons | LEGAL_BUTTON_MASK) != LEGAL_BUTTON_MASK) {
            throw new IllegalArgumentException("Invalid combination of button flags");
        }
    }
    
    public synchronized void mouseWheel(int wheelAmt) {
        peer.mouseWheel(wheelAmt);
        afterEvent();
    }
    
    public synchronized void keyPress(int keycode) {
        checkKeycodeArgument(keycode);
        peer.keyPress(keycode);
        afterEvent();
    }
    
    public synchronized void keyRelease(int keycode) {
        checkKeycodeArgument(keycode);
        peer.keyRelease(keycode);
        afterEvent();
    }
    
    private void checkKeycodeArgument(int keycode) {
        if (keycode == KeyEvent.VK_UNDEFINED) {
            throw new IllegalArgumentException("Invalid key code");
        }
    }
    
    public synchronized Color getPixelColor(int x, int y) {
        Color color = new Color(peer.getRGBPixel(x, y));
        return color;
    }
    
    public synchronized BufferedImage createScreenCapture(Rectangle screenRect) {
        checkScreenCaptureAllowed();
        checkValidRect(screenRect);
        BufferedImage image;
        DataBufferInt buffer;
        WritableRaster raster;
        if (screenCapCM == null) {
            screenCapCM = new DirectColorModel(24, 16711680, 65280, 255);
        }
        int[] pixels;
        int[] bandmasks = new int[3];
        pixels = peer.getRGBPixels(screenRect);
        buffer = new DataBufferInt(pixels, pixels.length);
        bandmasks[0] = screenCapCM.getRedMask();
        bandmasks[1] = screenCapCM.getGreenMask();
        bandmasks[2] = screenCapCM.getBlueMask();
        raster = Raster.createPackedRaster(buffer, screenRect.width, screenRect.height, screenRect.width, bandmasks, null);
        image = new BufferedImage(screenCapCM, raster, false, null);
        return image;
    }
    
    private static void checkValidRect(Rectangle rect) {
        if (rect.width <= 0 || rect.height <= 0) {
            throw new IllegalArgumentException("Rectangle width and height must be > 0");
        }
    }
    
    private static void checkScreenCaptureAllowed() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkPermission(SecurityConstants.READ_DISPLAY_PIXELS_PERMISSION);
        }
    }
    
    private void afterEvent() {
        autoWaitForIdle();
        autoDelay();
    }
    
    public synchronized boolean isAutoWaitForIdle() {
        return isAutoWaitForIdle;
    }
    
    public synchronized void setAutoWaitForIdle(boolean isOn) {
        isAutoWaitForIdle = isOn;
    }
    
    private void autoWaitForIdle() {
        if (isAutoWaitForIdle) {
            waitForIdle();
        }
    }
    
    public synchronized int getAutoDelay() {
        return autoDelay;
    }
    
    public synchronized void setAutoDelay(int ms) {
        checkDelayArgument(ms);
        autoDelay = ms;
    }
    
    private void autoDelay() {
        delay(autoDelay);
    }
    
    public synchronized void delay(int ms) {
        checkDelayArgument(ms);
        try {
            Thread.sleep(ms);
        } catch (InterruptedException ite) {
            ite.printStackTrace();
        }
    }
    
    private void checkDelayArgument(int ms) {
        if (ms < 0 || ms > MAX_DELAY) {
            throw new IllegalArgumentException("Delay must be to 0 to 60,000ms");
        }
    }
    
    public synchronized void waitForIdle() {
        checkNotDispatchThread();
        try {
            SunToolkit.flushPendingEvents();
            EventQueue.invokeAndWait(new Robot$1(this));
        } catch (InterruptedException ite) {
            System.err.println("Robot.waitForIdle, non-fatal exception caught:");
            ite.printStackTrace();
        } catch (InvocationTargetException ine) {
            System.err.println("Robot.waitForIdle, non-fatal exception caught:");
            ine.printStackTrace();
        }
    }
    
    private void checkNotDispatchThread() {
        if (EventQueue.isDispatchThread()) {
            throw new IllegalThreadStateException("Cannot call method from the event dispatcher thread");
        }
    }
    
    public synchronized String toString() {
        String params = "autoDelay = " + getAutoDelay() + ", " + "autoWaitForIdle = " + isAutoWaitForIdle();
        return getClass().getName() + "[ " + params + " ]";
    }
}
