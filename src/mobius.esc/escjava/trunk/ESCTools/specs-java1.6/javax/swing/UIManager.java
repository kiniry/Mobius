package javax.swing;

import java.awt.Component;
import java.awt.Font;
import java.awt.Color;
import java.awt.Insets;
import java.awt.Dimension;
import java.awt.KeyboardFocusManager;
import java.awt.Toolkit;
import java.security.AccessController;
import javax.swing.plaf.ComponentUI;
import javax.swing.border.Border;
import javax.swing.event.SwingPropertyChangeSupport;
import java.beans.PropertyChangeListener;
import java.io.Serializable;
import java.io.File;
import java.util.ArrayList;
import java.util.Properties;
import java.util.StringTokenizer;
import java.util.Vector;
import java.util.Locale;
import sun.security.action.GetPropertyAction;

public class UIManager implements Serializable {
    
    /*synthetic*/ static void access$200(Properties x0, String x1) {
        checkProperty(x0, x1);
    }
    
    /*synthetic*/ static String access$100() {
        return makeSwingPropertiesFilename();
    }
    
    public UIManager() {
        
    }
    {
    }
    private static final Object lafStateACKey = new StringBuffer("LookAndFeel State");
    private static final Object classLock = new Object();
    private static Thread currentLAFStateThread = null;
    private static UIManager$LAFState currentLAFState = null;
    
    private static UIManager$LAFState getLAFState() {
        Thread thisThread = Thread.currentThread();
        if (thisThread == currentLAFStateThread) {
            return currentLAFState;
        }
        UIManager$LAFState rv = (UIManager$LAFState)(UIManager$LAFState)SwingUtilities.appContextGet(lafStateACKey);
        if (rv == null) {
            synchronized (classLock) {
                rv = (UIManager$LAFState)(UIManager$LAFState)SwingUtilities.appContextGet(lafStateACKey);
                if (rv == null) {
                    SwingUtilities.appContextPut(lafStateACKey, (rv = new UIManager$LAFState(null)));
                }
            }
        }
        currentLAFStateThread = thisThread;
        currentLAFState = rv;
        return rv;
    }
    private static final String defaultLAFKey = "swing.defaultlaf";
    private static final String auxiliaryLAFsKey = "swing.auxiliarylaf";
    private static final String multiplexingLAFKey = "swing.plaf.multiplexinglaf";
    private static final String installedLAFsKey = "swing.installedlafs";
    private static final String disableMnemonicKey = "swing.disablenavaids";
    
    private static String makeInstalledLAFKey(String laf, String attr) {
        return "swing.installedlaf." + laf + "." + attr;
    }
    
    private static String makeSwingPropertiesFilename() {
        String sep = File.separator;
        String javaHome = System.getProperty("java.home");
        if (javaHome == null) {
            javaHome = "<java.home undefined>";
        }
        return javaHome + sep + "lib" + sep + "swing.properties";
    }
    {
    }
    private static UIManager$LookAndFeelInfo[] installedLAFs;
    static {
        ArrayList iLAFs = new ArrayList(4);
        iLAFs.add(new UIManager$LookAndFeelInfo("Metal", "javax.swing.plaf.metal.MetalLookAndFeel"));
        iLAFs.add(new UIManager$LookAndFeelInfo("CDE/Motif", "com.sun.java.swing.plaf.motif.MotifLookAndFeel"));
        String osName = (String)(String)AccessController.doPrivileged(new GetPropertyAction("os.name"));
        if (osName != null && osName.indexOf("Windows") != -1) {
            iLAFs.add(new UIManager$LookAndFeelInfo("Windows", "com.sun.java.swing.plaf.windows.WindowsLookAndFeel"));
            if (Toolkit.getDefaultToolkit().getDesktopProperty("win.xpstyle.themeActive") != null) {
                iLAFs.add(new UIManager$LookAndFeelInfo("Windows Classic", "com.sun.java.swing.plaf.windows.WindowsClassicLookAndFeel"));
            }
        } else {
            iLAFs.add(new UIManager$LookAndFeelInfo("GTK+", "com.sun.java.swing.plaf.gtk.GTKLookAndFeel"));
        }
        installedLAFs = (UIManager$LookAndFeelInfo[])(UIManager$LookAndFeelInfo[])iLAFs.toArray(new UIManager$LookAndFeelInfo[iLAFs.size()]);
    }
    
    public static UIManager$LookAndFeelInfo[] getInstalledLookAndFeels() {
        maybeInitialize();
        UIManager$LookAndFeelInfo[] ilafs = installedLAFs;
        UIManager$LookAndFeelInfo[] rv = new UIManager$LookAndFeelInfo[ilafs.length];
        System.arraycopy(ilafs, 0, rv, 0, ilafs.length);
        return rv;
    }
    
    public static void setInstalledLookAndFeels(UIManager$LookAndFeelInfo[] infos) throws SecurityException {
        UIManager$LookAndFeelInfo[] newInfos = new UIManager$LookAndFeelInfo[infos.length];
        System.arraycopy(infos, 0, newInfos, 0, infos.length);
        installedLAFs = newInfos;
    }
    
    public static void installLookAndFeel(UIManager$LookAndFeelInfo info) {
        UIManager$LookAndFeelInfo[] infos = getInstalledLookAndFeels();
        UIManager$LookAndFeelInfo[] newInfos = new UIManager$LookAndFeelInfo[infos.length + 1];
        System.arraycopy(infos, 0, newInfos, 0, infos.length);
        newInfos[infos.length] = info;
        setInstalledLookAndFeels(newInfos);
    }
    
    public static void installLookAndFeel(String name, String className) {
        installLookAndFeel(new UIManager$LookAndFeelInfo(name, className));
    }
    
    public static LookAndFeel getLookAndFeel() {
        maybeInitialize();
        return getLAFState().lookAndFeel;
    }
    
    public static void setLookAndFeel(LookAndFeel newLookAndFeel) throws UnsupportedLookAndFeelException {
        if ((newLookAndFeel != null) && !newLookAndFeel.isSupportedLookAndFeel()) {
            String s = newLookAndFeel.toString() + " not supported on this platform";
            throw new UnsupportedLookAndFeelException(s);
        }
        UIManager$LAFState lafState = getLAFState();
        LookAndFeel oldLookAndFeel = lafState.lookAndFeel;
        if (oldLookAndFeel != null) {
            oldLookAndFeel.uninitialize();
        }
        lafState.lookAndFeel = newLookAndFeel;
        if (newLookAndFeel != null) {
            sun.swing.DefaultLookup.setDefaultLookup(null);
            newLookAndFeel.initialize();
            lafState.setLookAndFeelDefaults(newLookAndFeel.getDefaults());
        } else {
            lafState.setLookAndFeelDefaults(null);
        }
        SwingPropertyChangeSupport changeSupport = lafState.getPropertyChangeSupport(false);
        if (changeSupport != null) {
            changeSupport.firePropertyChange("lookAndFeel", oldLookAndFeel, newLookAndFeel);
        }
    }
    
    public static void setLookAndFeel(String className) throws ClassNotFoundException, InstantiationException, IllegalAccessException, UnsupportedLookAndFeelException {
        if ("javax.swing.plaf.metal.MetalLookAndFeel".equals(className)) {
            setLookAndFeel(new javax.swing.plaf.metal.MetalLookAndFeel());
        } else {
            Class lnfClass = SwingUtilities.loadSystemClass(className);
            setLookAndFeel((LookAndFeel)((LookAndFeel)lnfClass.newInstance()));
        }
    }
    
    public static String getSystemLookAndFeelClassName() {
        String systemLAF = (String)(String)AccessController.doPrivileged(new GetPropertyAction("swing.systemlaf"));
        if (systemLAF != null) {
            return systemLAF;
        }
        String osName = (String)(String)AccessController.doPrivileged(new GetPropertyAction("os.name"));
        if (osName != null) {
            if (osName.indexOf("Windows") != -1) {
                return "com.sun.java.swing.plaf.windows.WindowsLookAndFeel";
            } else {
                String desktop = (String)(String)AccessController.doPrivileged(new GetPropertyAction("sun.desktop"));
                if ("gnome".equals(desktop)) {
                    return "com.sun.java.swing.plaf.gtk.GTKLookAndFeel";
                }
                if ((osName.indexOf("Solaris") != -1) || (osName.indexOf("SunOS") != -1)) {
                    return "com.sun.java.swing.plaf.motif.MotifLookAndFeel";
                }
            }
        }
        return getCrossPlatformLookAndFeelClassName();
    }
    
    public static String getCrossPlatformLookAndFeelClassName() {
        String laf = (String)(String)AccessController.doPrivileged(new GetPropertyAction("swing.crossplatformlaf"));
        if (laf != null) {
            return laf;
        }
        return "javax.swing.plaf.metal.MetalLookAndFeel";
    }
    
    public static UIDefaults getDefaults() {
        maybeInitialize();
        return getLAFState().multiUIDefaults;
    }
    
    public static Font getFont(Object key) {
        return getDefaults().getFont(key);
    }
    
    public static Font getFont(Object key, Locale l) {
        return getDefaults().getFont(key, l);
    }
    
    public static Color getColor(Object key) {
        return getDefaults().getColor(key);
    }
    
    public static Color getColor(Object key, Locale l) {
        return getDefaults().getColor(key, l);
    }
    
    public static Icon getIcon(Object key) {
        return getDefaults().getIcon(key);
    }
    
    public static Icon getIcon(Object key, Locale l) {
        return getDefaults().getIcon(key, l);
    }
    
    public static Border getBorder(Object key) {
        return getDefaults().getBorder(key);
    }
    
    public static Border getBorder(Object key, Locale l) {
        return getDefaults().getBorder(key, l);
    }
    
    public static String getString(Object key) {
        return getDefaults().getString(key);
    }
    
    public static String getString(Object key, Locale l) {
        return getDefaults().getString(key, l);
    }
    
    static String getString(Object key, Component c) {
        Locale l = (c == null) ? Locale.getDefault() : c.getLocale();
        return getString(key, l);
    }
    
    public static int getInt(Object key) {
        return getDefaults().getInt(key);
    }
    
    public static int getInt(Object key, Locale l) {
        return getDefaults().getInt(key, l);
    }
    
    static int getInt(Object key, int defaultValue) {
        Object value = UIManager.get(key);
        if (value instanceof Integer) {
            return ((Integer)(Integer)value).intValue();
        }
        if (value instanceof String) {
            try {
                return Integer.parseInt((String)(String)value);
            } catch (NumberFormatException nfe) {
            }
        }
        return defaultValue;
    }
    
    public static boolean getBoolean(Object key) {
        return getDefaults().getBoolean(key);
    }
    
    public static boolean getBoolean(Object key, Locale l) {
        return getDefaults().getBoolean(key, l);
    }
    
    public static Insets getInsets(Object key) {
        return getDefaults().getInsets(key);
    }
    
    public static Insets getInsets(Object key, Locale l) {
        return getDefaults().getInsets(key, l);
    }
    
    public static Dimension getDimension(Object key) {
        return getDefaults().getDimension(key);
    }
    
    public static Dimension getDimension(Object key, Locale l) {
        return getDefaults().getDimension(key, l);
    }
    
    public static Object get(Object key) {
        return getDefaults().get(key);
    }
    
    public static Object get(Object key, Locale l) {
        return getDefaults().get(key, l);
    }
    
    public static Object put(Object key, Object value) {
        return getDefaults().put(key, value);
    }
    
    public static ComponentUI getUI(JComponent target) {
        maybeInitialize();
        ComponentUI ui = null;
        LookAndFeel multiLAF = getLAFState().multiLookAndFeel;
        if (multiLAF != null) {
            ui = multiLAF.getDefaults().getUI(target);
        }
        if (ui == null) {
            ui = getDefaults().getUI(target);
        }
        return ui;
    }
    
    public static UIDefaults getLookAndFeelDefaults() {
        maybeInitialize();
        return getLAFState().getLookAndFeelDefaults();
    }
    
    private static LookAndFeel getMultiLookAndFeel() {
        LookAndFeel multiLookAndFeel = getLAFState().multiLookAndFeel;
        if (multiLookAndFeel == null) {
            String defaultName = "javax.swing.plaf.multi.MultiLookAndFeel";
            String className = getLAFState().swingProps.getProperty(multiplexingLAFKey, defaultName);
            try {
                Class lnfClass = SwingUtilities.loadSystemClass(className);
                multiLookAndFeel = (LookAndFeel)(LookAndFeel)lnfClass.newInstance();
            } catch (Exception exc) {
                System.err.println("UIManager: failed loading " + className);
            }
        }
        return multiLookAndFeel;
    }
    
    public static void addAuxiliaryLookAndFeel(LookAndFeel laf) {
        maybeInitialize();
        if (!laf.isSupportedLookAndFeel()) {
            return;
        }
        Vector v = getLAFState().auxLookAndFeels;
        if (v == null) {
            v = new Vector();
        }
        if (!v.contains(laf)) {
            v.addElement(laf);
            laf.initialize();
            getLAFState().auxLookAndFeels = v;
            if (getLAFState().multiLookAndFeel == null) {
                getLAFState().multiLookAndFeel = getMultiLookAndFeel();
            }
        }
    }
    
    public static boolean removeAuxiliaryLookAndFeel(LookAndFeel laf) {
        maybeInitialize();
        boolean result;
        Vector v = getLAFState().auxLookAndFeels;
        if ((v == null) || (v.size() == 0)) {
            return false;
        }
        result = v.removeElement(laf);
        if (result) {
            if (v.size() == 0) {
                getLAFState().auxLookAndFeels = null;
                getLAFState().multiLookAndFeel = null;
            } else {
                getLAFState().auxLookAndFeels = v;
            }
        }
        laf.uninitialize();
        return result;
    }
    
    public static LookAndFeel[] getAuxiliaryLookAndFeels() {
        maybeInitialize();
        Vector v = getLAFState().auxLookAndFeels;
        if ((v == null) || (v.size() == 0)) {
            return null;
        } else {
            LookAndFeel[] rv = new LookAndFeel[v.size()];
            for (int i = 0; i < rv.length; i++) {
                rv[i] = (LookAndFeel)(LookAndFeel)v.elementAt(i);
            }
            return rv;
        }
    }
    
    public static void addPropertyChangeListener(PropertyChangeListener listener) {
        synchronized (classLock) {
            getLAFState().getPropertyChangeSupport(true).addPropertyChangeListener(listener);
        }
    }
    
    public static void removePropertyChangeListener(PropertyChangeListener listener) {
        synchronized (classLock) {
            getLAFState().getPropertyChangeSupport(true).removePropertyChangeListener(listener);
        }
    }
    
    public static PropertyChangeListener[] getPropertyChangeListeners() {
        synchronized (classLock) {
            return getLAFState().getPropertyChangeSupport(true).getPropertyChangeListeners();
        }
    }
    
    private static Properties loadSwingProperties() {
        if (UIManager.class.getClassLoader() != null) {
            return new Properties();
        } else {
            final Properties props = new Properties();
            java.security.AccessController.doPrivileged(new UIManager$1(props));
            return props;
        }
    }
    
    private static void checkProperty(Properties props, String key) {
        String value = System.getProperty(key);
        if (value != null) {
            props.put(key, value);
        }
    }
    
    private static void initializeInstalledLAFs(Properties swingProps) {
        String ilafsString = swingProps.getProperty(installedLAFsKey);
        if (ilafsString == null) {
            return;
        }
        Vector lafs = new Vector();
        StringTokenizer st = new StringTokenizer(ilafsString, ",", false);
        while (st.hasMoreTokens()) {
            lafs.addElement(st.nextToken());
        }
        Vector ilafs = new Vector(lafs.size());
        for (int i = 0; i < lafs.size(); i++) {
            String laf = (String)(String)lafs.elementAt(i);
            String name = swingProps.getProperty(makeInstalledLAFKey(laf, "name"), laf);
            String cls = swingProps.getProperty(makeInstalledLAFKey(laf, "class"));
            if (cls != null) {
                ilafs.addElement(new UIManager$LookAndFeelInfo(name, cls));
            }
        }
        installedLAFs = new UIManager$LookAndFeelInfo[ilafs.size()];
        for (int i = 0; i < ilafs.size(); i++) {
            installedLAFs[i] = (UIManager$LookAndFeelInfo)((UIManager$LookAndFeelInfo)ilafs.elementAt(i));
        }
    }
    
    private static void initializeDefaultLAF(Properties swingProps) {
        if (getLAFState().lookAndFeel != null) {
            return;
        }
        String metalLnf = getCrossPlatformLookAndFeelClassName();
        String lnfDefault = metalLnf;
        String lnfName = "<undefined>";
        try {
            lnfName = swingProps.getProperty(defaultLAFKey, lnfDefault);
            setLookAndFeel(lnfName);
        } catch (Exception e) {
            try {
                lnfName = swingProps.getProperty(defaultLAFKey, metalLnf);
                setLookAndFeel(lnfName);
            } catch (Exception e2) {
                throw new Error("can\'t load " + lnfName);
            }
        }
    }
    
    private static void initializeAuxiliaryLAFs(Properties swingProps) {
        String auxLookAndFeelNames = swingProps.getProperty(auxiliaryLAFsKey);
        if (auxLookAndFeelNames == null) {
            return;
        }
        Vector auxLookAndFeels = new Vector();
        StringTokenizer p = new StringTokenizer(auxLookAndFeelNames, ",");
        String factoryName;
        while (p.hasMoreTokens()) {
            String className = p.nextToken();
            try {
                Class lnfClass = SwingUtilities.loadSystemClass(className);
                LookAndFeel newLAF = (LookAndFeel)(LookAndFeel)lnfClass.newInstance();
                newLAF.initialize();
                auxLookAndFeels.addElement(newLAF);
            } catch (Exception e) {
                System.err.println("UIManager: failed loading auxiliary look and feel " + className);
            }
        }
        if (auxLookAndFeels.size() == 0) {
            auxLookAndFeels = null;
        } else {
            getLAFState().multiLookAndFeel = getMultiLookAndFeel();
            if (getLAFState().multiLookAndFeel == null) {
                auxLookAndFeels = null;
            }
        }
        getLAFState().auxLookAndFeels = auxLookAndFeels;
    }
    
    private static void initializeSystemDefaults(Properties swingProps) {
        getLAFState().swingProps = swingProps;
    }
    
    private static void maybeInitialize() {
        synchronized (classLock) {
            if (!getLAFState().initialized) {
                getLAFState().initialized = true;
                initialize();
            }
        }
    }
    
    private static void initialize() {
        Properties swingProps = loadSwingProperties();
        initializeSystemDefaults(swingProps);
        initializeDefaultLAF(swingProps);
        initializeAuxiliaryLAFs(swingProps);
        initializeInstalledLAFs(swingProps);
        String toolkitName = Toolkit.getDefaultToolkit().getClass().getName();
        if (!"sun.awt.X11.XToolkit".equals(toolkitName)) {
            if (FocusManager.isFocusManagerEnabled()) {
                KeyboardFocusManager.getCurrentKeyboardFocusManager().setDefaultFocusTraversalPolicy(new LayoutFocusTraversalPolicy());
            }
        }
        KeyboardFocusManager.getCurrentKeyboardFocusManager().addKeyEventPostProcessor(new UIManager$2());
    }
}
