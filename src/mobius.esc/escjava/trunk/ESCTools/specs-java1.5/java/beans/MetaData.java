package java.beans;

import java.util.Vector;
import java.util.Hashtable;

class MetaData {
    
    MetaData() {
        
    }
    private static Hashtable internalPersistenceDelegates = new Hashtable();
    private static Hashtable transientProperties = new Hashtable();
    private static PersistenceDelegate nullPersistenceDelegate = new NullPersistenceDelegate();
    private static PersistenceDelegate primitivePersistenceDelegate = new PrimitivePersistenceDelegate();
    private static PersistenceDelegate defaultPersistenceDelegate = new DefaultPersistenceDelegate();
    private static PersistenceDelegate arrayPersistenceDelegate;
    private static PersistenceDelegate proxyPersistenceDelegate;
    static {
        registerConstructor("java.util.Date", new String[]{"time"});
        registerConstructor("java.beans.Statement", new String[]{"target", "methodName", "arguments"});
        registerConstructor("java.beans.Expression", new String[]{"target", "methodName", "arguments"});
        registerConstructor("java.beans.EventHandler", new String[]{"target", "action", "eventPropertyName", "listenerMethodName"});
        registerConstructor("java.awt.Point", new String[]{"x", "y"});
        registerConstructor("java.awt.Dimension", new String[]{"width", "height"});
        registerConstructor("java.awt.Rectangle", new String[]{"x", "y", "width", "height"});
        registerConstructor("java.awt.Insets", new String[]{"top", "left", "bottom", "right"});
        registerConstructor("java.awt.Color", new String[]{"red", "green", "blue", "alpha"});
        registerConstructor("java.awt.Font", new String[]{"name", "style", "size"});
        registerConstructor("java.awt.Cursor", new String[]{"type"});
        registerConstructor("java.awt.GridBagConstraints", new String[]{"gridx", "gridy", "gridwidth", "gridheight", "weightx", "weighty", "anchor", "fill", "insets", "ipadx", "ipady"});
        registerConstructor("java.awt.ScrollPane", new String[]{"scrollbarDisplayPolicy"});
        registerConstructor("javax.swing.plaf.FontUIResource", new String[]{"name", "style", "size"});
        registerConstructor("javax.swing.plaf.ColorUIResource", new String[]{"red", "green", "blue"});
        registerConstructor("javax.swing.tree.DefaultTreeModel", new String[]{"root"});
        registerConstructor("javax.swing.JTree", new String[]{"model"});
        registerConstructor("javax.swing.tree.TreePath", new String[]{"path"});
        registerConstructor("javax.swing.OverlayLayout", new String[]{"target"});
        registerConstructor("javax.swing.BoxLayout", new String[]{"target", "axis"});
        registerConstructor("javax.swing.Box$Filler", new String[]{"minimumSize", "preferredSize", "maximumSize"});
        registerConstructor("javax.swing.DefaultCellEditor", new String[]{"component"});
        registerConstructor("javax.swing.JSplitPane", new String[]{"orientation"});
        registerConstructor("javax.swing.ImageIcon", new String[]{"description"});
        registerConstructor("javax.swing.JButton", new String[]{"label"});
        registerConstructor("javax.swing.border.BevelBorder", new String[]{"bevelType", "highlightOuter", "highlightInner", "shadowOuter", "shadowInner"});
        registerConstructor("javax.swing.plaf.BorderUIResource$BevelBorderUIResource", new String[]{"bevelType", "highlightOuter", "highlightInner", "shadowOuter", "shadowInner"});
        registerConstructor("javax.swing.border.CompoundBorder", new String[]{"outsideBorder", "insideBorder"});
        registerConstructor("javax.swing.plaf.BorderUIResource$CompoundBorderUIResource", new String[]{"outsideBorder", "insideBorder"});
        registerConstructor("javax.swing.border.EmptyBorder", new String[]{"top", "left", "bottom", "right"});
        registerConstructor("javax.swing.plaf.BorderUIResource$EmptyBorderUIResource", new String[]{"top", "left", "bottom", "right"});
        registerConstructor("javax.swing.border.EtchedBorder", new String[]{"etchType", "highlight", "shadow"});
        registerConstructor("javax.swing.plaf.BorderUIResource$EtchedBorderUIResource", new String[]{"etchType", "highlight", "shadow"});
        registerConstructor("javax.swing.border.LineBorder", new String[]{"lineColor", "thickness"});
        registerConstructor("javax.swing.plaf.BorderUIResource$LineBorderUIResource", new String[]{"lineColor", "thickness"});
        registerConstructor("javax.swing.border.MatteBorder", new String[]{"top", "left", "bottom", "right", "tileIcon"});
        registerConstructor("javax.swing.plaf.BorderUIResource$MatteBorderUIResource", new String[]{"top", "left", "bottom", "right", "tileIcon"});
        registerConstructor("javax.swing.border.SoftBevelBorder", new String[]{"bevelType", "highlightOuter", "highlightInner", "shadowOuter", "shadowInner"});
        registerConstructor("javax.swing.border.TitledBorder", new String[]{"border", "title", "titleJustification", "titlePosition", "titleFont", "titleColor"});
        registerConstructor("javax.swing.plaf.BorderUIResource$TitledBorderUIResource", new String[]{"border", "title", "titleJustification", "titlePosition", "titleFont", "titleColor"});
        removeProperty("java.awt.geom.RectangularShape", "frame");
        removeProperty("java.awt.Rectangle", "bounds");
        removeProperty("java.awt.Dimension", "size");
        removeProperty("java.awt.Point", "location");
        removeProperty("java.awt.Component", "foreground");
        removeProperty("java.awt.Component", "background");
        removeProperty("java.awt.Component", "font");
        removeProperty("java.awt.Component", "visible");
        removeProperty("java.awt.ScrollPane", "scrollPosition");
        removeProperty("java.awt.im.InputContext", "compositionEnabled");
        removeProperty("javax.swing.JComponent", "minimumSize");
        removeProperty("javax.swing.JComponent", "preferredSize");
        removeProperty("javax.swing.JComponent", "maximumSize");
        removeProperty("javax.swing.ImageIcon", "image");
        removeProperty("javax.swing.ImageIcon", "imageObserver");
        removeProperty("javax.swing.JMenu", "accelerator");
        removeProperty("javax.swing.JMenuItem", "accelerator");
        removeProperty("javax.swing.JMenuBar", "helpMenu");
        removeProperty("javax.swing.JScrollPane", "verticalScrollBar");
        removeProperty("javax.swing.JScrollPane", "horizontalScrollBar");
        removeProperty("javax.swing.JScrollPane", "rowHeader");
        removeProperty("javax.swing.JScrollPane", "columnHeader");
        removeProperty("javax.swing.JViewport", "extentSize");
        removeProperty("javax.swing.table.JTableHeader", "defaultRenderer");
        removeProperty("javax.swing.JList", "cellRenderer");
        removeProperty("javax.swing.JList", "selectedIndices");
        removeProperty("javax.swing.DefaultListSelectionModel", "leadSelectionIndex");
        removeProperty("javax.swing.DefaultListSelectionModel", "anchorSelectionIndex");
        removeProperty("javax.swing.JComboBox", "selectedIndex");
        removeProperty("javax.swing.JTabbedPane", "selectedIndex");
        removeProperty("javax.swing.JTabbedPane", "selectedComponent");
        removeProperty("javax.swing.AbstractButton", "disabledIcon");
        removeProperty("javax.swing.JLabel", "disabledIcon");
        removeProperty("javax.swing.text.JTextComponent", "caret");
        removeProperty("javax.swing.text.JTextComponent", "caretPosition");
        removeProperty("javax.swing.text.JTextComponent", "selectionStart");
        removeProperty("javax.swing.text.JTextComponent", "selectionEnd");
    }
    
    static boolean equals(Object o1, Object o2) {
        return (o1 == null) ? (o2 == null) : o1.equals(o2);
    }
    
    public static synchronized void setPersistenceDelegate(Class type, PersistenceDelegate persistenceDelegate) {
        setBeanAttribute(type, "persistenceDelegate", persistenceDelegate);
    }
    
    public static synchronized PersistenceDelegate getPersistenceDelegate(Class type) {
        if (type == null) {
            return nullPersistenceDelegate;
        }
        if (ReflectionUtils.isPrimitive(type)) {
            return primitivePersistenceDelegate;
        }
        if (type.isArray()) {
            if (arrayPersistenceDelegate == null) {
                arrayPersistenceDelegate = new ArrayPersistenceDelegate();
            }
            return arrayPersistenceDelegate;
        }
        try {
            if (java.lang.reflect.Proxy.isProxyClass(type)) {
                if (proxyPersistenceDelegate == null) {
                    proxyPersistenceDelegate = new ProxyPersistenceDelegate();
                }
                return proxyPersistenceDelegate;
            }
        } catch (Exception e) {
        }
        String typeName = type.getName();
        if (getBeanAttribute(type, "transient_init") == null) {
            Vector tp = (Vector)(Vector)transientProperties.get(typeName);
            if (tp != null) {
                for (int i = 0; i < tp.size(); i++) {
                    setPropertyAttribute(type, (String)(String)tp.get(i), "transient", Boolean.TRUE);
                }
            }
            setBeanAttribute(type, "transient_init", Boolean.TRUE);
        }
        PersistenceDelegate pd = (PersistenceDelegate)(PersistenceDelegate)getBeanAttribute(type, "persistenceDelegate");
        if (pd == null) {
            pd = (PersistenceDelegate)(PersistenceDelegate)internalPersistenceDelegates.get(typeName);
            if (pd != null) {
                return pd;
            }
            internalPersistenceDelegates.put(typeName, defaultPersistenceDelegate);
            try {
                String name = type.getName();
                Class c = Class.forName("java.beans." + name.replace('.', '_') + "_PersistenceDelegate");
                pd = (PersistenceDelegate)(PersistenceDelegate)c.newInstance();
                internalPersistenceDelegates.put(typeName, pd);
            } catch (ClassNotFoundException e) {
            } catch (Exception e) {
                System.err.println("Internal error: " + e);
            }
        }
        return (pd != null) ? pd : defaultPersistenceDelegate;
    }
    
    public static BeanInfo getBeanInfo(Class type) {
        BeanInfo info = null;
        try {
            info = Introspector.getBeanInfo(type);
        } catch (Throwable e) {
            e.printStackTrace();
        }
        return info;
    }
    
    private static PropertyDescriptor getPropertyDescriptor(Class type, String propertyName) {
        BeanInfo info = getBeanInfo(type);
        PropertyDescriptor[] propertyDescriptors = info.getPropertyDescriptors();
        for (int i = 0; i < propertyDescriptors.length; i++) {
            PropertyDescriptor pd = propertyDescriptors[i];
            if (propertyName.equals(pd.getName())) {
                return pd;
            }
        }
        return null;
    }
    
    private static void setPropertyAttribute(Class type, String property, String attribute, Object value) {
        PropertyDescriptor pd = getPropertyDescriptor(type, property);
        if (pd == null) {
            System.err.println("Warning: property " + property + " is not defined on " + type);
            return;
        }
        pd.setValue(attribute, value);
    }
    
    private static void setBeanAttribute(Class type, String attribute, Object value) {
        getBeanInfo(type).getBeanDescriptor().setValue(attribute, value);
    }
    
    private static Object getBeanAttribute(Class type, String attribute) {
        return getBeanInfo(type).getBeanDescriptor().getValue(attribute);
    }
    
    private static synchronized void registerConstructor(String typeName, String[] constructor) {
        internalPersistenceDelegates.put(typeName, new DefaultPersistenceDelegate(constructor));
    }
    
    private static void removeProperty(String typeName, String property) {
        Vector tp = (Vector)(Vector)transientProperties.get(typeName);
        if (tp == null) {
            tp = new Vector();
            transientProperties.put(typeName, tp);
        }
        tp.add(property);
    }
}
