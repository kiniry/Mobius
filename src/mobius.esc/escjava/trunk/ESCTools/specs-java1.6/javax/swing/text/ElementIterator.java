package javax.swing.text;

import java.util.Stack;
import java.util.Enumeration;

public class ElementIterator implements Cloneable {
    {
    }
    private Element root;
    private Stack elementStack = null;
    {
    }
    
    public ElementIterator(Document document) {
        
        root = document.getDefaultRootElement();
    }
    
    public ElementIterator(Element root) {
        
        this.root = root;
    }
    
    public synchronized Object clone() {
        try {
            ElementIterator it = new ElementIterator(root);
            if (elementStack != null) {
                it.elementStack = new Stack();
                for (int i = 0; i < elementStack.size(); i++) {
                    ElementIterator$StackItem item = (ElementIterator$StackItem)(ElementIterator$StackItem)elementStack.elementAt(i);
                    ElementIterator$StackItem clonee = (ElementIterator$StackItem)(ElementIterator$StackItem)item.clone();
                    it.elementStack.push(clonee);
                }
            }
            return it;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public Element first() {
        if (root == null) {
            return null;
        }
        elementStack = new Stack();
        if (root.getElementCount() != 0) {
            elementStack.push(new ElementIterator$StackItem(this, root, null));
        }
        return root;
    }
    
    public int depth() {
        if (elementStack == null) {
            return 0;
        }
        return elementStack.size();
    }
    
    public Element current() {
        if (elementStack == null) {
            return first();
        }
        if (!elementStack.empty()) {
            ElementIterator$StackItem item = (ElementIterator$StackItem)(ElementIterator$StackItem)elementStack.peek();
            Element elem = ElementIterator.StackItem.access$100(item);
            int index = ElementIterator.StackItem.access$200(item);
            if (index == -1) {
                return elem;
            }
            return elem.getElement(index);
        }
        return null;
    }
    
    public Element next() {
        if (elementStack == null) {
            return first();
        }
        if (elementStack.isEmpty()) {
            return null;
        }
        ElementIterator$StackItem item = (ElementIterator$StackItem)(ElementIterator$StackItem)elementStack.peek();
        Element elem = ElementIterator.StackItem.access$100(item);
        int index = ElementIterator.StackItem.access$200(item);
        if (index + 1 < elem.getElementCount()) {
            Element child = elem.getElement(index + 1);
            if (child.isLeaf()) {
                ElementIterator.StackItem.access$300(item);
            } else {
                elementStack.push(new ElementIterator$StackItem(this, child, null));
            }
            return child;
        } else {
            elementStack.pop();
            if (!elementStack.isEmpty()) {
                ElementIterator$StackItem top = (ElementIterator$StackItem)(ElementIterator$StackItem)elementStack.peek();
                ElementIterator.StackItem.access$300(top);
                return next();
            }
        }
        return null;
    }
    
    public Element previous() {
        int stackSize;
        if (elementStack == null || (stackSize = elementStack.size()) == 0) {
            return null;
        }
        ElementIterator$StackItem item = (ElementIterator$StackItem)(ElementIterator$StackItem)elementStack.peek();
        Element elem = ElementIterator.StackItem.access$100(item);
        int index = ElementIterator.StackItem.access$200(item);
        if (index > 0) {
            return getDeepestLeaf(elem.getElement(--index));
        } else if (index == 0) {
            return elem;
        } else if (index == -1) {
            if (stackSize == 1) {
                return null;
            }
            Object top = elementStack.pop();
            item = (ElementIterator$StackItem)(ElementIterator$StackItem)elementStack.peek();
            elementStack.push(top);
            elem = ElementIterator.StackItem.access$100(item);
            index = ElementIterator.StackItem.access$200(item);
            return ((index == -1) ? elem : getDeepestLeaf(elem.getElement(index)));
        }
        return null;
    }
    
    private Element getDeepestLeaf(Element parent) {
        if (parent.isLeaf()) {
            return parent;
        }
        int childCount = parent.getElementCount();
        if (childCount == 0) {
            return parent;
        }
        return getDeepestLeaf(parent.getElement(childCount - 1));
    }
    
    private void dumpTree() {
        Element elem;
        while (true) {
            if ((elem = next()) != null) {
                System.out.println("elem: " + elem.getName());
                AttributeSet attr = elem.getAttributes();
                String s = "";
                Enumeration names = attr.getAttributeNames();
                while (names.hasMoreElements()) {
                    Object key = names.nextElement();
                    Object value = attr.getAttribute(key);
                    if (value instanceof AttributeSet) {
                        s = s + key + "=**AttributeSet** ";
                    } else {
                        s = s + key + "=" + value + " ";
                    }
                }
                System.out.println("attributes: " + s);
            } else {
                break;
            }
        }
    }
}
