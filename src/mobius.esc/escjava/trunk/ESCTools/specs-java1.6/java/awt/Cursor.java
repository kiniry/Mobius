package java.awt;

import java.awt.AWTException;
import java.awt.Toolkit;
import java.io.File;
import java.util.Hashtable;
import java.util.Properties;
import java.util.StringTokenizer;
import java.security.AccessController;
import sun.awt.DebugHelper;

public class Cursor implements java.io.Serializable {
    
    /*synthetic*/ static Properties access$300() {
        return systemCustomCursorProperties;
    }
    
    /*synthetic*/ static String access$200() {
        return systemCustomCursorPropertiesFile;
    }
    
    /*synthetic*/ static String access$100() {
        return systemCustomCursorDirPrefix;
    }
    
    /*synthetic*/ static void access$000(long x0) {
        finalizeImpl(x0);
    }
    public static final int DEFAULT_CURSOR = 0;
    public static final int CROSSHAIR_CURSOR = 1;
    public static final int TEXT_CURSOR = 2;
    public static final int WAIT_CURSOR = 3;
    public static final int SW_RESIZE_CURSOR = 4;
    public static final int SE_RESIZE_CURSOR = 5;
    public static final int NW_RESIZE_CURSOR = 6;
    public static final int NE_RESIZE_CURSOR = 7;
    public static final int N_RESIZE_CURSOR = 8;
    public static final int S_RESIZE_CURSOR = 9;
    public static final int W_RESIZE_CURSOR = 10;
    public static final int E_RESIZE_CURSOR = 11;
    public static final int HAND_CURSOR = 12;
    public static final int MOVE_CURSOR = 13;
    protected static Cursor[] predefined = new Cursor[14];
    static final String[][] cursorProperties = {{"AWT.DefaultCursor", "Default Cursor"}, {"AWT.CrosshairCursor", "Crosshair Cursor"}, {"AWT.TextCursor", "Text Cursor"}, {"AWT.WaitCursor", "Wait Cursor"}, {"AWT.SWResizeCursor", "Southwest Resize Cursor"}, {"AWT.SEResizeCursor", "Southeast Resize Cursor"}, {"AWT.NWResizeCursor", "Northwest Resize Cursor"}, {"AWT.NEResizeCursor", "Northeast Resize Cursor"}, {"AWT.NResizeCursor", "North Resize Cursor"}, {"AWT.SResizeCursor", "South Resize Cursor"}, {"AWT.WResizeCursor", "West Resize Cursor"}, {"AWT.EResizeCursor", "East Resize Cursor"}, {"AWT.HandCursor", "Hand Cursor"}, {"AWT.MoveCursor", "Move Cursor"}};
    int type = DEFAULT_CURSOR;
    public static final int CUSTOM_CURSOR = -1;
    private static final Hashtable systemCustomCursors = new Hashtable(1);
    private static final String systemCustomCursorDirPrefix = initCursorDir();
    
    private static String initCursorDir() {
        String jhome = (String)(String)java.security.AccessController.doPrivileged(new sun.security.action.GetPropertyAction("java.home"));
        return jhome + File.separator + "lib" + File.separator + "images" + File.separator + "cursors" + File.separator;
    }
    private static final String systemCustomCursorPropertiesFile = systemCustomCursorDirPrefix + "cursors.properties";
    private static Properties systemCustomCursorProperties = null;
    private static final String CursorDotPrefix = "Cursor.";
    private static final String DotFileSuffix = ".File";
    private static final String DotHotspotSuffix = ".HotSpot";
    private static final String DotNameSuffix = ".Name";
    private static final long serialVersionUID = 8028237497568985504L;
    private static final DebugHelper dbg = DebugHelper.create(Cursor.class);
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    private static native void initIDs();
    private transient long pData;
    private transient Object anchor = new Object();
    {
    }
    transient Cursor$CursorDisposer disposer;
    
    private void setPData(long pData) {
        this.pData = pData;
        if (!GraphicsEnvironment.isHeadless() && pData != 0) {
            if (disposer == null) {
                if (anchor == null) {
                    anchor = new Object();
                }
                disposer = new Cursor$CursorDisposer();
                sun.java2d.Disposer.addRecord(anchor, disposer);
            }
            disposer.pData = pData;
        }
    }
    protected String name;
    
    public static Cursor getPredefinedCursor(int type) {
        if (type < Cursor.DEFAULT_CURSOR || type > Cursor.MOVE_CURSOR) {
            throw new IllegalArgumentException("illegal cursor type");
        }
        if (predefined[type] == null) {
            predefined[type] = new Cursor(type);
        }
        return predefined[type];
    }
    
    public static Cursor getSystemCustomCursor(final String name) throws AWTException, HeadlessException {
        GraphicsEnvironment.checkHeadless();
        Cursor cursor = (Cursor)(Cursor)systemCustomCursors.get(name);
        if (cursor == null) {
            synchronized (systemCustomCursors) {
                if (systemCustomCursorProperties == null) loadSystemCustomCursorProperties();
            }
            String prefix = CursorDotPrefix + name;
            String key = prefix + DotFileSuffix;
            if (!systemCustomCursorProperties.containsKey(key)) {
                if (dbg.on) {
                    dbg.println("Cursor.getSystemCustomCursor(" + name + ") returned null");
                }
                return null;
            }
            final String fileName = systemCustomCursorProperties.getProperty(key);
            String localized = (String)systemCustomCursorProperties.getProperty(prefix + DotNameSuffix);
            if (localized == null) localized = name;
            String hotspot = (String)systemCustomCursorProperties.getProperty(prefix + DotHotspotSuffix);
            if (hotspot == null) throw new AWTException("no hotspot property defined for cursor: " + name);
            StringTokenizer st = new StringTokenizer(hotspot, ",");
            if (st.countTokens() != 2) throw new AWTException("failed to parse hotspot property for cursor: " + name);
            int x = 0;
            int y = 0;
            try {
                x = Integer.parseInt(st.nextToken());
                y = Integer.parseInt(st.nextToken());
            } catch (NumberFormatException nfe) {
                throw new AWTException("failed to parse hotspot property for cursor: " + name);
            }
            try {
                final int fx = x;
                final int fy = y;
                final String flocalized = localized;
                cursor = (Cursor)(Cursor)java.security.AccessController.doPrivileged(new Cursor$1(fileName, fx, fy, flocalized));
            } catch (Exception e) {
                throw new AWTException("Exception: " + e.getClass() + " " + e.getMessage() + " occurred while creating cursor " + name);
            }
            if (cursor == null) {
                if (dbg.on) {
                    dbg.println("Cursor.getSystemCustomCursor(" + name + ") returned null");
                }
            } else {
                systemCustomCursors.put(name, cursor);
            }
        }
        return cursor;
    }
    
    public static Cursor getDefaultCursor() {
        return getPredefinedCursor(Cursor.DEFAULT_CURSOR);
    }
    
    public Cursor(int type) {
        
        if (type < Cursor.DEFAULT_CURSOR || type > Cursor.MOVE_CURSOR) {
            throw new IllegalArgumentException("illegal cursor type");
        }
        this.type = type;
        name = Toolkit.getProperty(cursorProperties[type][0], cursorProperties[type][1]);
    }
    
    protected Cursor(String name) {
        
        this.type = Cursor.CUSTOM_CURSOR;
        this.name = name;
    }
    
    public int getType() {
        return type;
    }
    
    public String getName() {
        return name;
    }
    
    public String toString() {
        return getClass().getName() + "[" + getName() + "]";
    }
    
    private static void loadSystemCustomCursorProperties() throws AWTException {
        synchronized (systemCustomCursors) {
            systemCustomCursorProperties = new Properties();
            try {
                AccessController.doPrivileged(new Cursor$2());
            } catch (Exception e) {
                systemCustomCursorProperties = null;
                throw new AWTException("Exception: " + e.getClass() + " " + e.getMessage() + " occurred while loading: " + systemCustomCursorPropertiesFile);
            }
        }
    }
    
    private static native void finalizeImpl(long pData);
}
