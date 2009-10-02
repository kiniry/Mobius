package javax.swing.text;

import java.awt.*;
import java.util.*;
import java.io.*;
import javax.swing.SwingUtilities;
import javax.swing.event.ChangeListener;
import java.lang.ref.WeakReference;
import java.util.WeakHashMap;
import sun.font.FontManager;

public class StyleContext implements Serializable, AbstractDocument$AttributeContext {
    
    public static final StyleContext getDefaultStyleContext() {
        if (defaultContext == null) {
            defaultContext = new StyleContext();
        }
        return defaultContext;
    }
    private static StyleContext defaultContext;
    
    public StyleContext() {
        
        styles = new StyleContext$NamedStyle(this, null);
        addStyle(DEFAULT_STYLE, null);
    }
    
    public Style addStyle(String nm, Style parent) {
        Style style = new StyleContext$NamedStyle(this, nm, parent);
        if (nm != null) {
            styles.addAttribute(nm, style);
        }
        return style;
    }
    
    public void removeStyle(String nm) {
        styles.removeAttribute(nm);
    }
    
    public Style getStyle(String nm) {
        return (Style)(Style)styles.getAttribute(nm);
    }
    
    public Enumeration getStyleNames() {
        return styles.getAttributeNames();
    }
    
    public void addChangeListener(ChangeListener l) {
        styles.addChangeListener(l);
    }
    
    public void removeChangeListener(ChangeListener l) {
        styles.removeChangeListener(l);
    }
    
    public ChangeListener[] getChangeListeners() {
        return ((StyleContext$NamedStyle)(StyleContext$NamedStyle)styles).getChangeListeners();
    }
    
    public Font getFont(AttributeSet attr) {
        int style = Font.PLAIN;
        if (StyleConstants.isBold(attr)) {
            style |= Font.BOLD;
        }
        if (StyleConstants.isItalic(attr)) {
            style |= Font.ITALIC;
        }
        String family = StyleConstants.getFontFamily(attr);
        int size = StyleConstants.getFontSize(attr);
        if (StyleConstants.isSuperscript(attr) || StyleConstants.isSubscript(attr)) {
            size -= 2;
        }
        return getFont(family, style, size);
    }
    
    public Color getForeground(AttributeSet attr) {
        return StyleConstants.getForeground(attr);
    }
    
    public Color getBackground(AttributeSet attr) {
        return StyleConstants.getBackground(attr);
    }
    
    public Font getFont(String family, int style, int size) {
        fontSearch.setValue(family, style, size);
        Font f = (Font)(Font)fontTable.get(fontSearch);
        if (f == null) {
            Style defaultStyle = getStyle(StyleContext.DEFAULT_STYLE);
            if (defaultStyle != null) {
                final String FONT_ATTRIBUTE_KEY = "FONT_ATTRIBUTE_KEY";
                Font defaultFont = (Font)(Font)defaultStyle.getAttribute(FONT_ATTRIBUTE_KEY);
                if (defaultFont != null && defaultFont.getFamily().equalsIgnoreCase(family)) {
                    f = defaultFont.deriveFont(style, size);
                }
            }
            if (f == null) {
                f = new Font(family, style, size);
            }
            if (!FontManager.fontSupportsDefaultEncoding(f)) {
                f = FontManager.getCompositeFontUIResource(f);
            }
            StyleContext$FontKey key = new StyleContext$FontKey(family, style, size);
            fontTable.put(key, f);
        }
        return f;
    }
    
    public FontMetrics getFontMetrics(Font f) {
        return Toolkit.getDefaultToolkit().getFontMetrics(f);
    }
    
    public synchronized AttributeSet addAttribute(AttributeSet old, Object name, Object value) {
        if ((old.getAttributeCount() + 1) <= getCompressionThreshold()) {
            search.removeAttributes(search);
            search.addAttributes(old);
            search.addAttribute(name, value);
            reclaim(old);
            return getImmutableUniqueSet();
        }
        MutableAttributeSet ma = getMutableAttributeSet(old);
        ma.addAttribute(name, value);
        return ma;
    }
    
    public synchronized AttributeSet addAttributes(AttributeSet old, AttributeSet attr) {
        if ((old.getAttributeCount() + attr.getAttributeCount()) <= getCompressionThreshold()) {
            search.removeAttributes(search);
            search.addAttributes(old);
            search.addAttributes(attr);
            reclaim(old);
            return getImmutableUniqueSet();
        }
        MutableAttributeSet ma = getMutableAttributeSet(old);
        ma.addAttributes(attr);
        return ma;
    }
    
    public synchronized AttributeSet removeAttribute(AttributeSet old, Object name) {
        if ((old.getAttributeCount() - 1) <= getCompressionThreshold()) {
            search.removeAttributes(search);
            search.addAttributes(old);
            search.removeAttribute(name);
            reclaim(old);
            return getImmutableUniqueSet();
        }
        MutableAttributeSet ma = getMutableAttributeSet(old);
        ma.removeAttribute(name);
        return ma;
    }
    
    public synchronized AttributeSet removeAttributes(AttributeSet old, Enumeration names) {
        if (old.getAttributeCount() <= getCompressionThreshold()) {
            search.removeAttributes(search);
            search.addAttributes(old);
            search.removeAttributes(names);
            reclaim(old);
            return getImmutableUniqueSet();
        }
        MutableAttributeSet ma = getMutableAttributeSet(old);
        ma.removeAttributes(names);
        return ma;
    }
    
    public synchronized AttributeSet removeAttributes(AttributeSet old, AttributeSet attrs) {
        if (old.getAttributeCount() <= getCompressionThreshold()) {
            search.removeAttributes(search);
            search.addAttributes(old);
            search.removeAttributes(attrs);
            reclaim(old);
            return getImmutableUniqueSet();
        }
        MutableAttributeSet ma = getMutableAttributeSet(old);
        ma.removeAttributes(attrs);
        return ma;
    }
    
    public AttributeSet getEmptySet() {
        return SimpleAttributeSet.EMPTY;
    }
    
    public void reclaim(AttributeSet a) {
        if (SwingUtilities.isEventDispatchThread()) {
            attributesPool.size();
        }
    }
    
    protected int getCompressionThreshold() {
        return THRESHOLD;
    }
    
    protected StyleContext$SmallAttributeSet createSmallAttributeSet(AttributeSet a) {
        return new StyleContext$SmallAttributeSet(this, a);
    }
    
    protected MutableAttributeSet createLargeAttributeSet(AttributeSet a) {
        return new SimpleAttributeSet(a);
    }
    
    synchronized void removeUnusedSets() {
        attributesPool.size();
    }
    
    AttributeSet getImmutableUniqueSet() {
        StyleContext$SmallAttributeSet key = createSmallAttributeSet(search);
        WeakReference reference = (WeakReference)(WeakReference)attributesPool.get(key);
        StyleContext$SmallAttributeSet a;
        if (reference == null || (a = (StyleContext$SmallAttributeSet)(StyleContext$SmallAttributeSet)reference.get()) == null) {
            a = key;
            attributesPool.put(a, new WeakReference(a));
        }
        return a;
    }
    
    MutableAttributeSet getMutableAttributeSet(AttributeSet a) {
        if (a instanceof MutableAttributeSet && a != SimpleAttributeSet.EMPTY) {
            return (MutableAttributeSet)(MutableAttributeSet)a;
        }
        return createLargeAttributeSet(a);
    }
    
    public String toString() {
        removeUnusedSets();
        String s = "";
        Iterator iterator = attributesPool.keySet().iterator();
        while (iterator.hasNext()) {
            StyleContext$SmallAttributeSet set = (StyleContext$SmallAttributeSet)(StyleContext$SmallAttributeSet)iterator.next();
            s = s + set + "\n";
        }
        return s;
    }
    
    public void writeAttributes(ObjectOutputStream out, AttributeSet a) throws IOException {
        writeAttributeSet(out, a);
    }
    
    public void readAttributes(ObjectInputStream in, MutableAttributeSet a) throws ClassNotFoundException, IOException {
        readAttributeSet(in, a);
    }
    
    public static void writeAttributeSet(ObjectOutputStream out, AttributeSet a) throws IOException {
        int n = a.getAttributeCount();
        out.writeInt(n);
        Enumeration keys = a.getAttributeNames();
        while (keys.hasMoreElements()) {
            Object key = keys.nextElement();
            if (key instanceof Serializable) {
                out.writeObject(key);
            } else {
                Object ioFmt = freezeKeyMap.get(key);
                if (ioFmt == null) {
                    throw new NotSerializableException(key.getClass().getName() + " is not serializable as a key in an AttributeSet");
                }
                out.writeObject(ioFmt);
            }
            Object value = a.getAttribute(key);
            Object ioFmt = freezeKeyMap.get(value);
            if (value instanceof Serializable) {
                out.writeObject((ioFmt != null) ? ioFmt : value);
            } else {
                if (ioFmt == null) {
                    throw new NotSerializableException(value.getClass().getName() + " is not serializable as a value in an AttributeSet");
                }
                out.writeObject(ioFmt);
            }
        }
    }
    
    public static void readAttributeSet(ObjectInputStream in, MutableAttributeSet a) throws ClassNotFoundException, IOException {
        int n = in.readInt();
        for (int i = 0; i < n; i++) {
            Object key = in.readObject();
            Object value = in.readObject();
            if (thawKeyMap != null) {
                Object staticKey = thawKeyMap.get(key);
                if (staticKey != null) {
                    key = staticKey;
                }
                Object staticValue = thawKeyMap.get(value);
                if (staticValue != null) {
                    value = staticValue;
                }
            }
            a.addAttribute(key, value);
        }
    }
    
    public static void registerStaticAttributeKey(Object key) {
        String ioFmt = key.getClass().getName() + "." + key.toString();
        if (freezeKeyMap == null) {
            freezeKeyMap = new Hashtable();
            thawKeyMap = new Hashtable();
        }
        freezeKeyMap.put(key, ioFmt);
        thawKeyMap.put(ioFmt, key);
    }
    
    public static Object getStaticAttribute(Object key) {
        if (thawKeyMap == null || key == null) {
            return null;
        }
        return thawKeyMap.get(key);
    }
    
    public static Object getStaticAttributeKey(Object key) {
        return key.getClass().getName() + "." + key.toString();
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws IOException {
        removeUnusedSets();
        s.defaultWriteObject();
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        fontSearch = new StyleContext$FontKey(null, 0, 0);
        fontTable = new Hashtable();
        search = new SimpleAttributeSet();
        attributesPool = Collections.synchronizedMap(new WeakHashMap());
        s.defaultReadObject();
    }
    public static final String DEFAULT_STYLE = "default";
    private static Hashtable freezeKeyMap;
    private static Hashtable thawKeyMap;
    private Style styles;
    private transient StyleContext$FontKey fontSearch = new StyleContext$FontKey(null, 0, 0);
    private transient Hashtable fontTable = new Hashtable();
    private transient Map attributesPool = Collections.synchronizedMap(new WeakHashMap());
    private transient MutableAttributeSet search = new SimpleAttributeSet();
    private int unusedSets;
    static final int THRESHOLD = 9;
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    static {
        try {
            int n = StyleConstants.keys.length;
            for (int i = 0; i < n; i++) {
                StyleContext.registerStaticAttributeKey(StyleConstants.keys[i]);
            }
        } catch (Throwable e) {
            e.printStackTrace();
        }
    }
}
