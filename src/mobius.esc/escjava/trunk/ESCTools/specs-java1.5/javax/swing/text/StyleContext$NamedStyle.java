package javax.swing.text;

import java.awt.*;
import java.util.*;
import java.io.*;
import javax.swing.event.ChangeListener;
import javax.swing.event.EventListenerList;
import javax.swing.event.ChangeEvent;

public class StyleContext$NamedStyle implements Style, Serializable {
    /*synthetic*/ final StyleContext this$0;
    
    public StyleContext$NamedStyle(/*synthetic*/ final StyleContext this$0, String name, Style parent) {
        this.this$0 = this$0;
        
        attributes = this$0.getEmptySet();
        if (name != null) {
            setName(name);
        }
        if (parent != null) {
            setResolveParent(parent);
        }
    }
    
    public StyleContext$NamedStyle(/*synthetic*/ final StyleContext this$0, Style parent) {
        this(this$0, null, parent);
    }
    
    public StyleContext$NamedStyle(/*synthetic*/ final StyleContext this$0) {
        this.this$0 = this$0;
        
        attributes = this$0.getEmptySet();
    }
    
    public String toString() {
        return "NamedStyle:" + getName() + " " + attributes;
    }
    
    public String getName() {
        if (isDefined(StyleConstants.NameAttribute)) {
            return getAttribute(StyleConstants.NameAttribute).toString();
        }
        return null;
    }
    
    public void setName(String name) {
        if (name != null) {
            this.addAttribute(StyleConstants.NameAttribute, name);
        }
    }
    
    public void addChangeListener(ChangeListener l) {
        listenerList.add(ChangeListener.class, l);
    }
    
    public void removeChangeListener(ChangeListener l) {
        listenerList.remove(ChangeListener.class, l);
    }
    
    public ChangeListener[] getChangeListeners() {
        return (ChangeListener[])(ChangeListener[])listenerList.getListeners(ChangeListener.class);
    }
    
    protected void fireStateChanged() {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ChangeListener.class) {
                if (changeEvent == null) changeEvent = new ChangeEvent(this);
                ((ChangeListener)(ChangeListener)listeners[i + 1]).stateChanged(changeEvent);
            }
        }
    }
    
    public EventListener[] getListeners(Class listenerType) {
        return listenerList.getListeners(listenerType);
    }
    
    public int getAttributeCount() {
        return attributes.getAttributeCount();
    }
    
    public boolean isDefined(Object attrName) {
        return attributes.isDefined(attrName);
    }
    
    public boolean isEqual(AttributeSet attr) {
        return attributes.isEqual(attr);
    }
    
    public AttributeSet copyAttributes() {
        StyleContext$NamedStyle a = new StyleContext$NamedStyle(this$0);
        a.attributes = attributes.copyAttributes();
        return a;
    }
    
    public Object getAttribute(Object attrName) {
        return attributes.getAttribute(attrName);
    }
    
    public Enumeration getAttributeNames() {
        return attributes.getAttributeNames();
    }
    
    public boolean containsAttribute(Object name, Object value) {
        return attributes.containsAttribute(name, value);
    }
    
    public boolean containsAttributes(AttributeSet attrs) {
        return attributes.containsAttributes(attrs);
    }
    
    public AttributeSet getResolveParent() {
        return attributes.getResolveParent();
    }
    
    public void addAttribute(Object name, Object value) {
        StyleContext context = this$0;
        attributes = context.addAttribute(attributes, name, value);
        fireStateChanged();
    }
    
    public void addAttributes(AttributeSet attr) {
        StyleContext context = this$0;
        attributes = context.addAttributes(attributes, attr);
        fireStateChanged();
    }
    
    public void removeAttribute(Object name) {
        StyleContext context = this$0;
        attributes = context.removeAttribute(attributes, name);
        fireStateChanged();
    }
    
    public void removeAttributes(Enumeration names) {
        StyleContext context = this$0;
        attributes = context.removeAttributes(attributes, names);
        fireStateChanged();
    }
    
    public void removeAttributes(AttributeSet attrs) {
        StyleContext context = this$0;
        if (attrs == this) {
            attributes = context.getEmptySet();
        } else {
            attributes = context.removeAttributes(attributes, attrs);
        }
        fireStateChanged();
    }
    
    public void setResolveParent(AttributeSet parent) {
        if (parent != null) {
            addAttribute(StyleConstants.ResolveAttribute, parent);
        } else {
            removeAttribute(StyleConstants.ResolveAttribute);
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        StyleContext.writeAttributeSet(s, attributes);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        attributes = SimpleAttributeSet.EMPTY;
        StyleContext.readAttributeSet(s, this);
    }
    protected EventListenerList listenerList = new EventListenerList();
    protected transient ChangeEvent changeEvent = null;
    private transient AttributeSet attributes;
}
