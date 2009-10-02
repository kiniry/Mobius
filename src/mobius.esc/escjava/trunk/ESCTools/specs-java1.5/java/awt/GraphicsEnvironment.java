package java.awt;

import java.awt.image.BufferedImage;
import java.util.Locale;
import sun.java2d.HeadlessGraphicsEnvironment;
import sun.java2d.SunGraphicsEnvironment;

public abstract class GraphicsEnvironment {
    
    /*synthetic*/ static Boolean access$102(Boolean x0) {
        return defaultHeadless = x0;
    }
    
    /*synthetic*/ static Boolean access$002(Boolean x0) {
        return headless = x0;
    }
    private static GraphicsEnvironment localEnv;
    private static Boolean headless;
    private static Boolean defaultHeadless;
    
    protected GraphicsEnvironment() {
        
    }
    
    public static synchronized GraphicsEnvironment getLocalGraphicsEnvironment() {
        if (localEnv == null) {
            String nm = (String)(String)java.security.AccessController.doPrivileged(new sun.security.action.GetPropertyAction("java.awt.graphicsenv", null));
            try {
                localEnv = (GraphicsEnvironment)(GraphicsEnvironment)Class.forName(nm).newInstance();
                if (isHeadless()) {
                    localEnv = new HeadlessGraphicsEnvironment(localEnv);
                }
            } catch (ClassNotFoundException e) {
                throw new Error("Could not find class: " + nm);
            } catch (InstantiationException e) {
                throw new Error("Could not instantiate Graphics Environment: " + nm);
            } catch (IllegalAccessException e) {
                throw new Error("Could not access Graphics Environment: " + nm);
            }
        }
        return localEnv;
    }
    
    public static boolean isHeadless() {
        return getHeadlessProperty();
    }
    
    static String getHeadlessMessage() {
        if (headless == null) {
            getHeadlessProperty();
        }
        return defaultHeadless != Boolean.TRUE ? null : "\nNo X11 DISPLAY variable was set, but this program performed an operation which requires it.";
    }
    
    private static boolean getHeadlessProperty() {
        if (headless == null) {
            java.security.AccessController.doPrivileged(new GraphicsEnvironment$1());
        }
        return headless.booleanValue();
    }
    
    static void checkHeadless() throws HeadlessException {
        if (isHeadless()) {
            throw new HeadlessException();
        }
    }
    
    public boolean isHeadlessInstance() {
        return getHeadlessProperty();
    }
    
    public abstract GraphicsDevice[] getScreenDevices() throws HeadlessException;
    
    public abstract GraphicsDevice getDefaultScreenDevice() throws HeadlessException;
    
    public abstract Graphics2D createGraphics(BufferedImage img);
    
    public abstract Font[] getAllFonts();
    
    public abstract String[] getAvailableFontFamilyNames();
    
    public abstract String[] getAvailableFontFamilyNames(Locale l);
    
    public void preferLocaleFonts() {
        sun.font.FontManager.preferLocaleFonts();
    }
    
    public void preferProportionalFonts() {
        sun.font.FontManager.preferProportionalFonts();
    }
    
    public Point getCenterPoint() throws HeadlessException {
        Rectangle usableBounds = SunGraphicsEnvironment.getUsableBounds(getDefaultScreenDevice());
        return new Point((usableBounds.width / 2) + usableBounds.x, (usableBounds.height / 2) + usableBounds.y);
    }
    
    public Rectangle getMaximumWindowBounds() throws HeadlessException {
        return SunGraphicsEnvironment.getUsableBounds(getDefaultScreenDevice());
    }
}
