package javax.swing.text.html;

import java.util.*;
import java.awt.*;
import java.io.*;
import java.net.*;
import javax.swing.ImageIcon;
import javax.swing.border.*;
import javax.swing.text.*;

public class StyleSheet extends StyleContext {
    
    /*synthetic*/ static CSS access$000(StyleSheet x0) {
        return x0.css;
    }
    {
    }
    
    public StyleSheet() {
        
        selectorMapping = new StyleSheet$SelectorMapping(0);
        resolvedStyles = new Hashtable();
        if (css == null) {
            css = new CSS();
        }
    }
    
    public Style getRule(HTML$Tag t, Element e) {
        StyleSheet$SearchBuffer sb = StyleSheet$SearchBuffer.obtainSearchBuffer();
        try {
            Vector searchContext = sb.getVector();
            for (Element p = e; p != null; p = p.getParentElement()) {
                searchContext.addElement(p);
            }
            int n = searchContext.size();
            StringBuffer cacheLookup = sb.getStringBuffer();
            AttributeSet attr;
            String eName;
            Object name;
            for (int counter = n - 1; counter >= 1; counter--) {
                e = (Element)(Element)searchContext.elementAt(counter);
                attr = e.getAttributes();
                name = attr.getAttribute(StyleConstants.NameAttribute);
                eName = name.toString();
                cacheLookup.append(eName);
                if (attr != null) {
                    if (attr.isDefined(HTML$Attribute.ID)) {
                        cacheLookup.append('#');
                        cacheLookup.append(attr.getAttribute(HTML$Attribute.ID));
                    } else if (attr.isDefined(HTML$Attribute.CLASS)) {
                        cacheLookup.append('.');
                        cacheLookup.append(attr.getAttribute(HTML$Attribute.CLASS));
                    }
                }
                cacheLookup.append(' ');
            }
            cacheLookup.append(t.toString());
            e = (Element)(Element)searchContext.elementAt(0);
            attr = e.getAttributes();
            if (e.isLeaf()) {
                Object testAttr = attr.getAttribute(t);
                if (testAttr instanceof AttributeSet) {
                    attr = (AttributeSet)(AttributeSet)testAttr;
                } else {
                    attr = null;
                }
            }
            if (attr != null) {
                if (attr.isDefined(HTML$Attribute.ID)) {
                    cacheLookup.append('#');
                    cacheLookup.append(attr.getAttribute(HTML$Attribute.ID));
                } else if (attr.isDefined(HTML$Attribute.CLASS)) {
                    cacheLookup.append('.');
                    cacheLookup.append(attr.getAttribute(HTML$Attribute.CLASS));
                }
            }
            Style style = getResolvedStyle(cacheLookup.toString(), searchContext, t);
            return style;
        } finally {
            StyleSheet$SearchBuffer.releaseSearchBuffer(sb);
        }
    }
    
    public Style getRule(String selector) {
        selector = cleanSelectorString(selector);
        if (selector != null) {
            Style style = getResolvedStyle(selector);
            return style;
        }
        return null;
    }
    
    public void addRule(String rule) {
        if (rule != null) {
            final String baseUnitsDisable = "BASE_SIZE_DISABLE";
            final String baseUnits = "BASE_SIZE ";
            final String w3cLengthUnitsEnable = "W3C_LENGTH_UNITS_ENABLE";
            final String w3cLengthUnitsDisable = "W3C_LENGTH_UNITS_DISABLE";
            if (rule == baseUnitsDisable) {
                sizeMap = sizeMapDefault;
            } else if (rule.startsWith(baseUnits)) {
                rebaseSizeMap(Integer.parseInt(rule.substring(baseUnits.length())));
            } else if (rule == w3cLengthUnitsEnable) {
                w3cLengthUnits = true;
            } else if (rule == w3cLengthUnitsDisable) {
                w3cLengthUnits = false;
            } else {
                StyleSheet$CssParser parser = new StyleSheet$CssParser(this);
                try {
                    parser.parse(getBase(), new StringReader(rule), false, false);
                } catch (IOException ioe) {
                }
            }
        }
    }
    
    public AttributeSet getDeclaration(String decl) {
        if (decl == null) {
            return SimpleAttributeSet.EMPTY;
        }
        StyleSheet$CssParser parser = new StyleSheet$CssParser(this);
        return parser.parseDeclaration(decl);
    }
    
    public void loadRules(Reader in, URL ref) throws IOException {
        StyleSheet$CssParser parser = new StyleSheet$CssParser(this);
        parser.parse(ref, in, false, false);
    }
    
    public AttributeSet getViewAttributes(View v) {
        return new StyleSheet$ViewAttributeSet(this, v);
    }
    
    public void removeStyle(String nm) {
        Style aStyle = getStyle(nm);
        if (aStyle != null) {
            String selector = cleanSelectorString(nm);
            String[] selectors = getSimpleSelectors(selector);
            synchronized (this) {
                StyleSheet$SelectorMapping mapping = getRootSelectorMapping();
                for (int i = selectors.length - 1; i >= 0; i--) {
                    mapping = mapping.getChildSelectorMapping(selectors[i], true);
                }
                Style rule = mapping.getStyle();
                if (rule != null) {
                    mapping.setStyle(null);
                    if (resolvedStyles.size() > 0) {
                        Enumeration values = resolvedStyles.elements();
                        while (values.hasMoreElements()) {
                            StyleSheet$ResolvedStyle style = (StyleSheet$ResolvedStyle)(StyleSheet$ResolvedStyle)values.nextElement();
                            style.removeStyle(rule);
                        }
                    }
                }
            }
        }
        super.removeStyle(nm);
    }
    
    public void addStyleSheet(StyleSheet ss) {
        synchronized (this) {
            if (linkedStyleSheets == null) {
                linkedStyleSheets = new Vector();
            }
            if (!linkedStyleSheets.contains(ss)) {
                int index = 0;
                if (ss instanceof javax.swing.plaf.UIResource && linkedStyleSheets.size() > 1) {
                    index = linkedStyleSheets.size() - 1;
                }
                linkedStyleSheets.insertElementAt(ss, index);
                linkStyleSheetAt(ss, index);
            }
        }
    }
    
    public void removeStyleSheet(StyleSheet ss) {
        synchronized (this) {
            if (linkedStyleSheets != null) {
                int index = linkedStyleSheets.indexOf(ss);
                if (index != -1) {
                    linkedStyleSheets.removeElementAt(index);
                    unlinkStyleSheet(ss, index);
                    if (index == 0 && linkedStyleSheets.size() == 0) {
                        linkedStyleSheets = null;
                    }
                }
            }
        }
    }
    
    public StyleSheet[] getStyleSheets() {
        StyleSheet[] retValue;
        synchronized (this) {
            if (linkedStyleSheets != null) {
                retValue = new StyleSheet[linkedStyleSheets.size()];
                linkedStyleSheets.copyInto(retValue);
            } else {
                retValue = null;
            }
        }
        return retValue;
    }
    
    public void importStyleSheet(URL url) {
        try {
            InputStream is;
            is = url.openStream();
            Reader r = new BufferedReader(new InputStreamReader(is));
            StyleSheet$CssParser parser = new StyleSheet$CssParser(this);
            parser.parse(url, r, false, true);
            r.close();
            is.close();
        } catch (Throwable e) {
        }
    }
    
    public void setBase(URL base) {
        this.base = base;
    }
    
    public URL getBase() {
        return base;
    }
    
    public void addCSSAttribute(MutableAttributeSet attr, CSS$Attribute key, String value) {
        css.addInternalCSSValue(attr, key, value);
    }
    
    public boolean addCSSAttributeFromHTML(MutableAttributeSet attr, CSS$Attribute key, String value) {
        Object iValue = css.getCssValue(key, value);
        if (iValue != null) {
            attr.addAttribute(key, iValue);
            return true;
        }
        return false;
    }
    
    public AttributeSet translateHTMLToCSS(AttributeSet htmlAttrSet) {
        AttributeSet cssAttrSet = css.translateHTMLToCSS(htmlAttrSet);
        MutableAttributeSet cssStyleSet = addStyle(null, null);
        cssStyleSet.addAttributes(cssAttrSet);
        return cssStyleSet;
    }
    
    public AttributeSet addAttribute(AttributeSet old, Object key, Object value) {
        if (css == null) {
            css = new CSS();
        }
        if (key instanceof StyleConstants) {
            HTML$Tag tag = HTML.getTagForStyleConstantsKey((StyleConstants)(StyleConstants)key);
            if (tag != null && old.isDefined(tag)) {
                old = removeAttribute(old, tag);
            }
            Object cssValue = css.styleConstantsValueToCSSValue((StyleConstants)(StyleConstants)key, value);
            if (cssValue != null) {
                Object cssKey = css.styleConstantsKeyToCSSKey((StyleConstants)(StyleConstants)key);
                if (cssKey != null) {
                    return super.addAttribute(old, cssKey, cssValue);
                }
            }
        }
        return super.addAttribute(old, key, value);
    }
    
    public AttributeSet addAttributes(AttributeSet old, AttributeSet attr) {
        if (!(attr instanceof HTMLDocument$TaggedAttributeSet)) {
            old = removeHTMLTags(old, attr);
        }
        return super.addAttributes(old, convertAttributeSet(attr));
    }
    
    public AttributeSet removeAttribute(AttributeSet old, Object key) {
        if (key instanceof StyleConstants) {
            HTML$Tag tag = HTML.getTagForStyleConstantsKey((StyleConstants)(StyleConstants)key);
            if (tag != null) {
                old = super.removeAttribute(old, tag);
            }
            Object cssKey = css.styleConstantsKeyToCSSKey((StyleConstants)(StyleConstants)key);
            if (cssKey != null) {
                return super.removeAttribute(old, cssKey);
            }
        }
        return super.removeAttribute(old, key);
    }
    
    public AttributeSet removeAttributes(AttributeSet old, Enumeration names) {
        return super.removeAttributes(old, names);
    }
    
    public AttributeSet removeAttributes(AttributeSet old, AttributeSet attrs) {
        if (old != attrs) {
            old = removeHTMLTags(old, attrs);
        }
        return super.removeAttributes(old, convertAttributeSet(attrs));
    }
    
    protected StyleContext$SmallAttributeSet createSmallAttributeSet(AttributeSet a) {
        return new StyleSheet$SmallConversionSet(this, a);
    }
    
    protected MutableAttributeSet createLargeAttributeSet(AttributeSet a) {
        return new StyleSheet$LargeConversionSet(this, a);
    }
    
    private AttributeSet removeHTMLTags(AttributeSet old, AttributeSet attr) {
        if (!(attr instanceof StyleSheet$LargeConversionSet) && !(attr instanceof StyleSheet$SmallConversionSet)) {
            Enumeration names = attr.getAttributeNames();
            while (names.hasMoreElements()) {
                Object key = names.nextElement();
                if (key instanceof StyleConstants) {
                    HTML$Tag tag = HTML.getTagForStyleConstantsKey((StyleConstants)(StyleConstants)key);
                    if (tag != null && old.isDefined(tag)) {
                        old = super.removeAttribute(old, tag);
                    }
                }
            }
        }
        return old;
    }
    
    AttributeSet convertAttributeSet(AttributeSet a) {
        if ((a instanceof StyleSheet$LargeConversionSet) || (a instanceof StyleSheet$SmallConversionSet)) {
            return a;
        }
        Enumeration names = a.getAttributeNames();
        while (names.hasMoreElements()) {
            Object name = names.nextElement();
            if (name instanceof StyleConstants) {
                MutableAttributeSet converted = new StyleSheet$LargeConversionSet(this);
                Enumeration keys = a.getAttributeNames();
                while (keys.hasMoreElements()) {
                    Object key = keys.nextElement();
                    Object cssValue = null;
                    if (key instanceof StyleConstants) {
                        Object cssKey = css.styleConstantsKeyToCSSKey((StyleConstants)(StyleConstants)key);
                        if (cssKey != null) {
                            Object value = a.getAttribute(key);
                            cssValue = css.styleConstantsValueToCSSValue((StyleConstants)(StyleConstants)key, value);
                            if (cssValue != null) {
                                converted.addAttribute(cssKey, cssValue);
                            }
                        }
                    }
                    if (cssValue == null) {
                        converted.addAttribute(key, a.getAttribute(key));
                    }
                }
                return converted;
            }
        }
        return a;
    }
    {
    }
    {
    }
    
    public Font getFont(AttributeSet a) {
        return css.getFont(this, a, 12, this);
    }
    
    public Color getForeground(AttributeSet a) {
        Color c = css.getColor(a, CSS$Attribute.COLOR);
        if (c == null) {
            return Color.black;
        }
        return c;
    }
    
    public Color getBackground(AttributeSet a) {
        return css.getColor(a, CSS$Attribute.BACKGROUND_COLOR);
    }
    
    public StyleSheet$BoxPainter getBoxPainter(AttributeSet a) {
        return new StyleSheet$BoxPainter(a, css, this);
    }
    
    public StyleSheet$ListPainter getListPainter(AttributeSet a) {
        return new StyleSheet$ListPainter(a, this);
    }
    
    public void setBaseFontSize(int sz) {
        css.setBaseFontSize(sz);
    }
    
    public void setBaseFontSize(String size) {
        css.setBaseFontSize(size);
    }
    
    public static int getIndexOfSize(float pt) {
        return CSS.getIndexOfSize(pt, sizeMapDefault);
    }
    
    public float getPointSize(int index) {
        return css.getPointSize(index, this);
    }
    
    public float getPointSize(String size) {
        return css.getPointSize(size, this);
    }
    
    public Color stringToColor(String string) {
        return CSS.stringToColor(string);
    }
    
    ImageIcon getBackgroundImage(AttributeSet attr) {
        Object value = attr.getAttribute(CSS$Attribute.BACKGROUND_IMAGE);
        if (value != null) {
            return ((CSS$BackgroundImage)(CSS$BackgroundImage)value).getImage(getBase());
        }
        return null;
    }
    
    void addRule(String[] selector, AttributeSet declaration, boolean isLinked) {
        int n = selector.length;
        StringBuffer sb = new StringBuffer();
        sb.append(selector[0]);
        for (int counter = 1; counter < n; counter++) {
            sb.append(' ');
            sb.append(selector[counter]);
        }
        String selectorName = sb.toString();
        Style rule = getStyle(selectorName);
        if (rule == null) {
            Style altRule = addStyle(selectorName, null);
            synchronized (this) {
                StyleSheet$SelectorMapping mapping = getRootSelectorMapping();
                for (int i = n - 1; i >= 0; i--) {
                    mapping = mapping.getChildSelectorMapping(selector[i], true);
                }
                rule = mapping.getStyle();
                if (rule == null) {
                    rule = altRule;
                    mapping.setStyle(rule);
                    refreshResolvedRules(selectorName, selector, rule, mapping.getSpecificity());
                }
            }
        }
        if (isLinked) {
            rule = getLinkedStyle(rule);
        }
        rule.addAttributes(declaration);
    }
    
    private synchronized void linkStyleSheetAt(StyleSheet ss, int index) {
        if (resolvedStyles.size() > 0) {
            Enumeration values = resolvedStyles.elements();
            while (values.hasMoreElements()) {
                StyleSheet$ResolvedStyle rule = (StyleSheet$ResolvedStyle)(StyleSheet$ResolvedStyle)values.nextElement();
                rule.insertExtendedStyleAt(ss.getRule(rule.getName()), index);
            }
        }
    }
    
    private synchronized void unlinkStyleSheet(StyleSheet ss, int index) {
        if (resolvedStyles.size() > 0) {
            Enumeration values = resolvedStyles.elements();
            while (values.hasMoreElements()) {
                StyleSheet$ResolvedStyle rule = (StyleSheet$ResolvedStyle)(StyleSheet$ResolvedStyle)values.nextElement();
                rule.removeExtendedStyleAt(index);
            }
        }
    }
    
    String[] getSimpleSelectors(String selector) {
        selector = cleanSelectorString(selector);
        StyleSheet$SearchBuffer sb = StyleSheet$SearchBuffer.obtainSearchBuffer();
        Vector selectors = sb.getVector();
        int lastIndex = 0;
        int length = selector.length();
        while (lastIndex != -1) {
            int newIndex = selector.indexOf(' ', lastIndex);
            if (newIndex != -1) {
                selectors.addElement(selector.substring(lastIndex, newIndex));
                if (++newIndex == length) {
                    lastIndex = -1;
                } else {
                    lastIndex = newIndex;
                }
            } else {
                selectors.addElement(selector.substring(lastIndex));
                lastIndex = -1;
            }
        }
        String[] retValue = new String[selectors.size()];
        selectors.copyInto(retValue);
        StyleSheet$SearchBuffer.releaseSearchBuffer(sb);
        return retValue;
    }
    
    String cleanSelectorString(String selector) {
        boolean lastWasSpace = true;
        for (int counter = 0, maxCounter = selector.length(); counter < maxCounter; counter++) {
            switch (selector.charAt(counter)) {
            case ' ': 
                if (lastWasSpace) {
                    return _cleanSelectorString(selector);
                }
                lastWasSpace = true;
                break;
            
            case '\n': 
            
            case '\r': 
            
            case '\t': 
                return _cleanSelectorString(selector);
            
            default: 
                lastWasSpace = false;
            
            }
        }
        if (lastWasSpace) {
            return _cleanSelectorString(selector);
        }
        return selector;
    }
    
    private String _cleanSelectorString(String selector) {
        StyleSheet$SearchBuffer sb = StyleSheet$SearchBuffer.obtainSearchBuffer();
        StringBuffer buff = sb.getStringBuffer();
        boolean lastWasSpace = true;
        int lastIndex = 0;
        char[] chars = selector.toCharArray();
        int numChars = chars.length;
        String retValue = null;
        try {
            for (int counter = 0; counter < numChars; counter++) {
                switch (chars[counter]) {
                case ' ': 
                    if (!lastWasSpace) {
                        lastWasSpace = true;
                        if (lastIndex < counter) {
                            buff.append(chars, lastIndex, 1 + counter - lastIndex);
                        }
                    }
                    lastIndex = counter + 1;
                    break;
                
                case '\n': 
                
                case '\r': 
                
                case '\t': 
                    if (!lastWasSpace) {
                        lastWasSpace = true;
                        if (lastIndex < counter) {
                            buff.append(chars, lastIndex, counter - lastIndex);
                            buff.append(' ');
                        }
                    }
                    lastIndex = counter + 1;
                    break;
                
                default: 
                    lastWasSpace = false;
                    break;
                
                }
            }
            if (lastWasSpace && buff.length() > 0) {
                buff.setLength(buff.length() - 1);
            } else if (lastIndex < numChars) {
                buff.append(chars, lastIndex, numChars - lastIndex);
            }
            retValue = buff.toString();
        } finally {
            StyleSheet$SearchBuffer.releaseSearchBuffer(sb);
        }
        return retValue;
    }
    
    private StyleSheet$SelectorMapping getRootSelectorMapping() {
        return selectorMapping;
    }
    
    static int getSpecificity(String selector) {
        int specificity = 0;
        boolean lastWasSpace = true;
        for (int counter = 0, maxCounter = selector.length(); counter < maxCounter; counter++) {
            switch (selector.charAt(counter)) {
            case '.': 
                specificity += 100;
                break;
            
            case '#': 
                specificity += 10000;
                break;
            
            case ' ': 
                lastWasSpace = true;
                break;
            
            default: 
                if (lastWasSpace) {
                    lastWasSpace = false;
                    specificity += 1;
                }
            
            }
        }
        return specificity;
    }
    
    private Style getLinkedStyle(Style localStyle) {
        Style retStyle = (Style)(Style)localStyle.getResolveParent();
        if (retStyle == null) {
            retStyle = addStyle(null, null);
            localStyle.setResolveParent(retStyle);
        }
        return retStyle;
    }
    
    private synchronized Style getResolvedStyle(String selector, Vector elements, HTML$Tag t) {
        Style retStyle = (Style)(Style)resolvedStyles.get(selector);
        if (retStyle == null) {
            retStyle = createResolvedStyle(selector, elements, t);
        }
        return retStyle;
    }
    
    private synchronized Style getResolvedStyle(String selector) {
        Style retStyle = (Style)(Style)resolvedStyles.get(selector);
        if (retStyle == null) {
            retStyle = createResolvedStyle(selector);
        }
        return retStyle;
    }
    
    private void addSortedStyle(StyleSheet$SelectorMapping mapping, Vector elements) {
        int size = elements.size();
        if (size > 0) {
            int specificity = mapping.getSpecificity();
            for (int counter = 0; counter < size; counter++) {
                if (specificity >= ((StyleSheet$SelectorMapping)(StyleSheet$SelectorMapping)elements.elementAt(counter)).getSpecificity()) {
                    elements.insertElementAt(mapping, counter);
                    return;
                }
            }
        }
        elements.addElement(mapping);
    }
    
    private synchronized void getStyles(StyleSheet$SelectorMapping parentMapping, Vector styles, String[] tags, String[] ids, String[] classes, int index, int numElements, Hashtable alreadyChecked) {
        if (alreadyChecked.contains(parentMapping)) {
            return;
        }
        alreadyChecked.put(parentMapping, parentMapping);
        Style style = parentMapping.getStyle();
        if (style != null) {
            addSortedStyle(parentMapping, styles);
        }
        for (int counter = index; counter < numElements; counter++) {
            String tagString = tags[counter];
            if (tagString != null) {
                StyleSheet$SelectorMapping childMapping = parentMapping.getChildSelectorMapping(tagString, false);
                if (childMapping != null) {
                    getStyles(childMapping, styles, tags, ids, classes, counter + 1, numElements, alreadyChecked);
                }
                if (classes[counter] != null) {
                    String className = classes[counter];
                    childMapping = parentMapping.getChildSelectorMapping(tagString + "." + className, false);
                    if (childMapping != null) {
                        getStyles(childMapping, styles, tags, ids, classes, counter + 1, numElements, alreadyChecked);
                    }
                    childMapping = parentMapping.getChildSelectorMapping("." + className, false);
                    if (childMapping != null) {
                        getStyles(childMapping, styles, tags, ids, classes, counter + 1, numElements, alreadyChecked);
                    }
                }
                if (ids[counter] != null) {
                    String idName = ids[counter];
                    childMapping = parentMapping.getChildSelectorMapping(tagString + "#" + idName, false);
                    if (childMapping != null) {
                        getStyles(childMapping, styles, tags, ids, classes, counter + 1, numElements, alreadyChecked);
                    }
                    childMapping = parentMapping.getChildSelectorMapping("#" + idName, false);
                    if (childMapping != null) {
                        getStyles(childMapping, styles, tags, ids, classes, counter + 1, numElements, alreadyChecked);
                    }
                }
            }
        }
    }
    
    private synchronized Style createResolvedStyle(String selector, String[] tags, String[] ids, String[] classes) {
        StyleSheet$SearchBuffer sb = StyleSheet$SearchBuffer.obtainSearchBuffer();
        Vector tempVector = sb.getVector();
        Hashtable tempHashtable = sb.getHashtable();
        try {
            StyleSheet$SelectorMapping mapping = getRootSelectorMapping();
            int numElements = tags.length;
            String tagString = tags[0];
            StyleSheet$SelectorMapping childMapping = mapping.getChildSelectorMapping(tagString, false);
            if (childMapping != null) {
                getStyles(childMapping, tempVector, tags, ids, classes, 1, numElements, tempHashtable);
            }
            if (classes[0] != null) {
                String className = classes[0];
                childMapping = mapping.getChildSelectorMapping(tagString + "." + className, false);
                if (childMapping != null) {
                    getStyles(childMapping, tempVector, tags, ids, classes, 1, numElements, tempHashtable);
                }
                childMapping = mapping.getChildSelectorMapping("." + className, false);
                if (childMapping != null) {
                    getStyles(childMapping, tempVector, tags, ids, classes, 1, numElements, tempHashtable);
                }
            }
            if (ids[0] != null) {
                String idName = ids[0];
                childMapping = mapping.getChildSelectorMapping(tagString + "#" + idName, false);
                if (childMapping != null) {
                    getStyles(childMapping, tempVector, tags, ids, classes, 1, numElements, tempHashtable);
                }
                childMapping = mapping.getChildSelectorMapping("#" + idName, false);
                if (childMapping != null) {
                    getStyles(childMapping, tempVector, tags, ids, classes, 1, numElements, tempHashtable);
                }
            }
            int numLinkedSS = (linkedStyleSheets != null) ? linkedStyleSheets.size() : 0;
            int numStyles = tempVector.size();
            AttributeSet[] attrs = new AttributeSet[numStyles + numLinkedSS];
            for (int counter = 0; counter < numStyles; counter++) {
                attrs[counter] = ((StyleSheet$SelectorMapping)(StyleSheet$SelectorMapping)tempVector.elementAt(counter)).getStyle();
            }
            for (int counter = 0; counter < numLinkedSS; counter++) {
                AttributeSet attr = ((StyleSheet)(StyleSheet)linkedStyleSheets.elementAt(counter)).getRule(selector);
                if (attr == null) {
                    attrs[counter + numStyles] = SimpleAttributeSet.EMPTY;
                } else {
                    attrs[counter + numStyles] = attr;
                }
            }
            StyleSheet$ResolvedStyle retStyle = new StyleSheet$ResolvedStyle(selector, attrs, numStyles);
            resolvedStyles.put(selector, retStyle);
            return retStyle;
        } finally {
            StyleSheet$SearchBuffer.releaseSearchBuffer(sb);
        }
    }
    
    private Style createResolvedStyle(String selector, Vector elements, HTML$Tag t) {
        int numElements = elements.size();
        String[] tags = new String[numElements];
        String[] ids = new String[numElements];
        String[] classes = new String[numElements];
        for (int counter = 0; counter < numElements; counter++) {
            Element e = (Element)(Element)elements.elementAt(counter);
            AttributeSet attr = e.getAttributes();
            if (counter == 0 && e.isLeaf()) {
                Object testAttr = attr.getAttribute(t);
                if (testAttr instanceof AttributeSet) {
                    attr = (AttributeSet)(AttributeSet)testAttr;
                } else {
                    attr = null;
                }
            }
            if (attr != null) {
                HTML$Tag tag = (HTML$Tag)(HTML$Tag)attr.getAttribute(StyleConstants.NameAttribute);
                if (tag != null) {
                    tags[counter] = tag.toString();
                } else {
                    tags[counter] = null;
                }
                if (attr.isDefined(HTML$Attribute.CLASS)) {
                    classes[counter] = attr.getAttribute(HTML$Attribute.CLASS).toString();
                } else {
                    classes[counter] = null;
                }
                if (attr.isDefined(HTML$Attribute.ID)) {
                    ids[counter] = attr.getAttribute(HTML$Attribute.ID).toString();
                } else {
                    ids[counter] = null;
                }
            } else {
                tags[counter] = ids[counter] = classes[counter] = null;
            }
        }
        tags[0] = t.toString();
        return createResolvedStyle(selector, tags, ids, classes);
    }
    
    private Style createResolvedStyle(String selector) {
        StyleSheet$SearchBuffer sb = StyleSheet$SearchBuffer.obtainSearchBuffer();
        Vector elements = sb.getVector();
        try {
            boolean done;
            int dotIndex = 0;
            int spaceIndex = 0;
            int poundIndex = 0;
            int lastIndex = 0;
            int length = selector.length();
            while (lastIndex < length) {
                if (dotIndex == lastIndex) {
                    dotIndex = selector.indexOf('.', lastIndex);
                }
                if (poundIndex == lastIndex) {
                    poundIndex = selector.indexOf('#', lastIndex);
                }
                spaceIndex = selector.indexOf(' ', lastIndex);
                if (spaceIndex == -1) {
                    spaceIndex = length;
                }
                if (dotIndex != -1 && poundIndex != -1 && dotIndex < spaceIndex && poundIndex < spaceIndex) {
                    if (poundIndex < dotIndex) {
                        if (lastIndex == poundIndex) {
                            elements.addElement("");
                        } else {
                            elements.addElement(selector.substring(lastIndex, poundIndex));
                        }
                        if ((dotIndex + 1) < spaceIndex) {
                            elements.addElement(selector.substring(dotIndex + 1, spaceIndex));
                        } else {
                            elements.addElement(null);
                        }
                        if ((poundIndex + 1) == dotIndex) {
                            elements.addElement(null);
                        } else {
                            elements.addElement(selector.substring(poundIndex + 1, dotIndex));
                        }
                    } else if (poundIndex < spaceIndex) {
                        if (lastIndex == dotIndex) {
                            elements.addElement("");
                        } else {
                            elements.addElement(selector.substring(lastIndex, dotIndex));
                        }
                        if ((dotIndex + 1) < poundIndex) {
                            elements.addElement(selector.substring(dotIndex + 1, poundIndex));
                        } else {
                            elements.addElement(null);
                        }
                        if ((poundIndex + 1) == spaceIndex) {
                            elements.addElement(null);
                        } else {
                            elements.addElement(selector.substring(poundIndex + 1, spaceIndex));
                        }
                    }
                    dotIndex = poundIndex = spaceIndex + 1;
                } else if (dotIndex != -1 && dotIndex < spaceIndex) {
                    if (dotIndex == lastIndex) {
                        elements.addElement("");
                    } else {
                        elements.addElement(selector.substring(lastIndex, dotIndex));
                    }
                    if ((dotIndex + 1) == spaceIndex) {
                        elements.addElement(null);
                    } else {
                        elements.addElement(selector.substring(dotIndex + 1, spaceIndex));
                    }
                    elements.addElement(null);
                    dotIndex = spaceIndex + 1;
                } else if (poundIndex != -1 && poundIndex < spaceIndex) {
                    if (poundIndex == lastIndex) {
                        elements.addElement("");
                    } else {
                        elements.addElement(selector.substring(lastIndex, poundIndex));
                    }
                    elements.addElement(null);
                    if ((poundIndex + 1) == spaceIndex) {
                        elements.addElement(null);
                    } else {
                        elements.addElement(selector.substring(poundIndex + 1, spaceIndex));
                    }
                    poundIndex = spaceIndex + 1;
                } else {
                    elements.addElement(selector.substring(lastIndex, spaceIndex));
                    elements.addElement(null);
                    elements.addElement(null);
                }
                lastIndex = spaceIndex + 1;
            }
            int total = elements.size();
            int numTags = total / 3;
            String[] tags = new String[numTags];
            String[] ids = new String[numTags];
            String[] classes = new String[numTags];
            for (int index = 0, eIndex = total - 3; index < numTags; index++, eIndex -= 3) {
                tags[index] = (String)(String)elements.elementAt(eIndex);
                classes[index] = (String)(String)elements.elementAt(eIndex + 1);
                ids[index] = (String)(String)elements.elementAt(eIndex + 2);
            }
            return createResolvedStyle(selector, tags, ids, classes);
        } finally {
            StyleSheet$SearchBuffer.releaseSearchBuffer(sb);
        }
    }
    
    private synchronized void refreshResolvedRules(String selectorName, String[] selector, Style newStyle, int specificity) {
        if (resolvedStyles.size() > 0) {
            Enumeration values = resolvedStyles.elements();
            while (values.hasMoreElements()) {
                StyleSheet$ResolvedStyle style = (StyleSheet$ResolvedStyle)(StyleSheet$ResolvedStyle)values.nextElement();
                if (style.matches(selectorName)) {
                    style.insertStyle(newStyle, specificity);
                }
            }
        }
    }
    {
    }
    static final Border noBorder = new EmptyBorder(0, 0, 0, 0);
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
    {
    }
    static final int DEFAULT_FONT_SIZE = 3;
    private CSS css;
    private StyleSheet$SelectorMapping selectorMapping;
    private Hashtable resolvedStyles;
    private Vector linkedStyleSheets;
    private URL base;
    {
    }
    
    void rebaseSizeMap(int base) {
        final int minimalFontSize = 4;
        sizeMap = new int[sizeMapDefault.length];
        for (int i = 0; i < sizeMapDefault.length; i++) {
            sizeMap[i] = Math.max(base * sizeMapDefault[i] / sizeMapDefault[CSS.baseFontSizeIndex], minimalFontSize);
        }
    }
    
    int[] getSizeMap() {
        return sizeMap;
    }
    
    boolean isW3CLengthUnits() {
        return w3cLengthUnits;
    }
    static int[] sizeMapDefault = {8, 10, 12, 14, 18, 24, 36};
    private int[] sizeMap = sizeMapDefault;
    private boolean w3cLengthUnits = false;
}
