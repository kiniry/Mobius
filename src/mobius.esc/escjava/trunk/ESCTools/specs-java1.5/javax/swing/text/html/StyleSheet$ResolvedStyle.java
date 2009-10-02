package javax.swing.text.html;

import java.util.*;
import java.awt.*;
import java.io.*;
import java.net.*;
import javax.swing.border.*;
import javax.swing.event.ChangeListener;
import javax.swing.text.*;

class StyleSheet$ResolvedStyle extends MuxingAttributeSet implements Serializable, Style {
    
    StyleSheet$ResolvedStyle(String name, AttributeSet[] attrs, int extendedIndex) {
        super(attrs);
        this.name = name;
        this.extendedIndex = extendedIndex;
    }
    
    synchronized void insertStyle(Style style, int specificity) {
        AttributeSet[] attrs = getAttributes();
        int maxCounter = attrs.length;
        int counter = 0;
        for (; counter < extendedIndex; counter++) {
            if (specificity > StyleSheet.getSpecificity(((Style)(Style)attrs[counter]).getName())) {
                break;
            }
        }
        insertAttributeSetAt(style, counter);
        extendedIndex++;
    }
    
    synchronized void removeStyle(Style style) {
        AttributeSet[] attrs = getAttributes();
        for (int counter = attrs.length - 1; counter >= 0; counter--) {
            if (attrs[counter] == style) {
                removeAttributeSetAt(counter);
                if (counter < extendedIndex) {
                    extendedIndex--;
                }
                break;
            }
        }
    }
    
    synchronized void insertExtendedStyleAt(Style attr, int index) {
        insertAttributeSetAt(attr, extendedIndex + index);
    }
    
    synchronized void addExtendedStyle(Style attr) {
        insertAttributeSetAt(attr, getAttributes().length);
    }
    
    synchronized void removeExtendedStyleAt(int index) {
        removeAttributeSetAt(extendedIndex + index);
    }
    
    protected boolean matches(String selector) {
        int sLast = selector.length();
        if (sLast == 0) {
            return false;
        }
        int thisLast = name.length();
        int sCurrent = selector.lastIndexOf(' ');
        int thisCurrent = name.lastIndexOf(' ');
        if (sCurrent >= 0) {
            sCurrent++;
        }
        if (thisCurrent >= 0) {
            thisCurrent++;
        }
        if (!matches(selector, sCurrent, sLast, thisCurrent, thisLast)) {
            return false;
        }
        while (sCurrent != -1) {
            sLast = sCurrent - 1;
            sCurrent = selector.lastIndexOf(' ', sLast - 1);
            if (sCurrent >= 0) {
                sCurrent++;
            }
            boolean match = false;
            while (!match && thisCurrent != -1) {
                thisLast = thisCurrent - 1;
                thisCurrent = name.lastIndexOf(' ', thisLast - 1);
                if (thisCurrent >= 0) {
                    thisCurrent++;
                }
                match = matches(selector, sCurrent, sLast, thisCurrent, thisLast);
            }
            if (!match) {
                return false;
            }
        }
        return true;
    }
    
    boolean matches(String selector, int sCurrent, int sLast, int thisCurrent, int thisLast) {
        sCurrent = Math.max(sCurrent, 0);
        thisCurrent = Math.max(thisCurrent, 0);
        int thisDotIndex = boundedIndexOf(name, '.', thisCurrent, thisLast);
        int thisPoundIndex = boundedIndexOf(name, '#', thisCurrent, thisLast);
        int sDotIndex = boundedIndexOf(selector, '.', sCurrent, sLast);
        int sPoundIndex = boundedIndexOf(selector, '#', sCurrent, sLast);
        if (sDotIndex != -1) {
            if (thisDotIndex == -1) {
                return false;
            }
            if (sCurrent == sDotIndex) {
                if ((thisLast - thisDotIndex) != (sLast - sDotIndex) || !selector.regionMatches(sCurrent, name, thisDotIndex, (thisLast - thisDotIndex))) {
                    return false;
                }
            } else {
                if ((sLast - sCurrent) != (thisLast - thisCurrent) || !selector.regionMatches(sCurrent, name, thisCurrent, (thisLast - thisCurrent))) {
                    return false;
                }
            }
            return true;
        }
        if (sPoundIndex != -1) {
            if (thisPoundIndex == -1) {
                return false;
            }
            if (sCurrent == sPoundIndex) {
                if ((thisLast - thisPoundIndex) != (sLast - sPoundIndex) || !selector.regionMatches(sCurrent, name, thisPoundIndex, (thisLast - thisPoundIndex))) {
                    return false;
                }
            } else {
                if ((sLast - sCurrent) != (thisLast - thisCurrent) || !selector.regionMatches(sCurrent, name, thisCurrent, (thisLast - thisCurrent))) {
                    return false;
                }
            }
            return true;
        }
        if (thisDotIndex != -1) {
            return (((thisDotIndex - thisCurrent) == (sLast - sCurrent)) && selector.regionMatches(sCurrent, name, thisCurrent, thisDotIndex - thisCurrent));
        }
        if (thisPoundIndex != -1) {
            return (((thisPoundIndex - thisCurrent) == (sLast - sCurrent)) && selector.regionMatches(sCurrent, name, thisCurrent, thisPoundIndex - thisCurrent));
        }
        return (((thisLast - thisCurrent) == (sLast - sCurrent)) && selector.regionMatches(sCurrent, name, thisCurrent, thisLast - thisCurrent));
    }
    
    int boundedIndexOf(String string, char search, int start, int end) {
        int retValue = string.indexOf(search, start);
        if (retValue >= end) {
            return -1;
        }
        return retValue;
    }
    
    public void addAttribute(Object name, Object value) {
    }
    
    public void addAttributes(AttributeSet attributes) {
    }
    
    public void removeAttribute(Object name) {
    }
    
    public void removeAttributes(Enumeration names) {
    }
    
    public void removeAttributes(AttributeSet attributes) {
    }
    
    public void setResolveParent(AttributeSet parent) {
    }
    
    public String getName() {
        return name;
    }
    
    public void addChangeListener(ChangeListener l) {
    }
    
    public void removeChangeListener(ChangeListener l) {
    }
    
    public ChangeListener[] getChangeListeners() {
        return new ChangeListener[0];
    }
    String name;
    private int extendedIndex;
}
