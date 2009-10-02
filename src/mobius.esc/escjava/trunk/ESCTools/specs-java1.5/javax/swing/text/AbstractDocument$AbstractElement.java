package javax.swing.text;

import java.util.*;
import java.io.*;
import javax.swing.undo.*;
import javax.swing.event.*;
import javax.swing.tree.TreeNode;

public abstract class AbstractDocument$AbstractElement implements Element, MutableAttributeSet, Serializable, TreeNode {
    /*synthetic*/ final AbstractDocument this$0;
    
    public AbstractDocument$AbstractElement(/*synthetic*/ final AbstractDocument this$0, Element parent, AttributeSet a) {
        this.this$0 = this$0;
        
        this.parent = parent;
        attributes = this$0.getAttributeContext().getEmptySet();
        if (a != null) {
            addAttributes(a);
        }
    }
    
    private final void indent(PrintWriter out, int n) {
        for (int i = 0; i < n; i++) {
            out.print("  ");
        }
    }
    
    public void dump(PrintStream psOut, int indentAmount) {
        PrintWriter out;
        try {
            out = new PrintWriter(new OutputStreamWriter(psOut, "JavaEsc"), true);
        } catch (UnsupportedEncodingException e) {
            out = new PrintWriter(psOut, true);
        }
        indent(out, indentAmount);
        if (getName() == null) {
            out.print("<??");
        } else {
            out.print("<" + getName());
        }
        if (getAttributeCount() > 0) {
            out.println("");
            Enumeration names = attributes.getAttributeNames();
            while (names.hasMoreElements()) {
                Object name = names.nextElement();
                indent(out, indentAmount + 1);
                out.println(name + "=" + getAttribute(name));
            }
            indent(out, indentAmount);
        }
        out.println(">");
        if (isLeaf()) {
            indent(out, indentAmount + 1);
            out.print("[" + getStartOffset() + "," + getEndOffset() + "]");
            AbstractDocument$Content c = this$0.getContent();
            try {
                String contentStr = c.getString(getStartOffset(), getEndOffset() - getStartOffset());
                if (contentStr.length() > 40) {
                    contentStr = contentStr.substring(0, 40) + "...";
                }
                out.println("[" + contentStr + "]");
            } catch (BadLocationException e) {
                ;
            }
        } else {
            int n = getElementCount();
            for (int i = 0; i < n; i++) {
                AbstractDocument$AbstractElement e = (AbstractDocument$AbstractElement)(AbstractDocument$AbstractElement)getElement(i);
                e.dump(psOut, indentAmount + 1);
            }
        }
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
        return attributes.copyAttributes();
    }
    
    public Object getAttribute(Object attrName) {
        Object value = attributes.getAttribute(attrName);
        if (value == null) {
            AttributeSet a = (parent != null) ? parent.getAttributes() : null;
            if (a != null) {
                value = a.getAttribute(attrName);
            }
        }
        return value;
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
        AttributeSet a = attributes.getResolveParent();
        if ((a == null) && (parent != null)) {
            a = parent.getAttributes();
        }
        return a;
    }
    
    public void addAttribute(Object name, Object value) {
        checkForIllegalCast();
        AbstractDocument$AttributeContext context = this$0.getAttributeContext();
        attributes = context.addAttribute(attributes, name, value);
    }
    
    public void addAttributes(AttributeSet attr) {
        checkForIllegalCast();
        AbstractDocument$AttributeContext context = this$0.getAttributeContext();
        attributes = context.addAttributes(attributes, attr);
    }
    
    public void removeAttribute(Object name) {
        checkForIllegalCast();
        AbstractDocument$AttributeContext context = this$0.getAttributeContext();
        attributes = context.removeAttribute(attributes, name);
    }
    
    public void removeAttributes(Enumeration names) {
        checkForIllegalCast();
        AbstractDocument$AttributeContext context = this$0.getAttributeContext();
        attributes = context.removeAttributes(attributes, names);
    }
    
    public void removeAttributes(AttributeSet attrs) {
        checkForIllegalCast();
        AbstractDocument$AttributeContext context = this$0.getAttributeContext();
        if (attrs == this) {
            attributes = context.getEmptySet();
        } else {
            attributes = context.removeAttributes(attributes, attrs);
        }
    }
    
    public void setResolveParent(AttributeSet parent) {
        checkForIllegalCast();
        AbstractDocument$AttributeContext context = this$0.getAttributeContext();
        if (parent != null) {
            attributes = context.addAttribute(attributes, StyleConstants.ResolveAttribute, parent);
        } else {
            attributes = context.removeAttribute(attributes, StyleConstants.ResolveAttribute);
        }
    }
    
    private final void checkForIllegalCast() {
        Thread t = this$0.getCurrentWriter();
        if ((t == null) || (t != Thread.currentThread())) {
            throw new StateInvariantError("Illegal cast to MutableAttributeSet");
        }
    }
    
    public Document getDocument() {
        return this$0;
    }
    
    public Element getParentElement() {
        return parent;
    }
    
    public AttributeSet getAttributes() {
        return this;
    }
    
    public String getName() {
        if (attributes.isDefined("$ename")) {
            return (String)(String)attributes.getAttribute("$ename");
        }
        return null;
    }
    
    public abstract int getStartOffset();
    
    public abstract int getEndOffset();
    
    public abstract Element getElement(int index);
    
    public abstract int getElementCount();
    
    public abstract int getElementIndex(int offset);
    
    public abstract boolean isLeaf();
    
    public TreeNode getChildAt(int childIndex) {
        return (TreeNode)(TreeNode)getElement(childIndex);
    }
    
    public int getChildCount() {
        return getElementCount();
    }
    
    public TreeNode getParent() {
        return (TreeNode)(TreeNode)getParentElement();
    }
    
    public int getIndex(TreeNode node) {
        for (int counter = getChildCount() - 1; counter >= 0; counter--) if (getChildAt(counter) == node) return counter;
        return -1;
    }
    
    public abstract boolean getAllowsChildren();
    
    public abstract Enumeration children();
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        StyleContext.writeAttributeSet(s, attributes);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        MutableAttributeSet attr = new SimpleAttributeSet();
        StyleContext.readAttributeSet(s, attr);
        AbstractDocument$AttributeContext context = this$0.getAttributeContext();
        attributes = context.addAttributes(SimpleAttributeSet.EMPTY, attr);
    }
    private Element parent;
    private transient AttributeSet attributes;
}
