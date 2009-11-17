package javax.swing.text;

import java.util.Stack;
import java.util.Vector;
import java.util.ArrayList;
import java.io.Serializable;
import javax.swing.event.*;

public class DefaultStyledDocument$ElementBuffer implements Serializable {
    /*synthetic*/ final DefaultStyledDocument this$0;
    
    public DefaultStyledDocument$ElementBuffer(/*synthetic*/ final DefaultStyledDocument this$0, Element root) {
        this.this$0 = this$0;
        
        this.root = root;
        changes = new Vector();
        path = new Stack();
    }
    
    public Element getRootElement() {
        return root;
    }
    
    public void insert(int offset, int length, DefaultStyledDocument$ElementSpec[] data, AbstractDocument$DefaultDocumentEvent de) {
        if (length == 0) {
            return;
        }
        insertOp = true;
        beginEdits(offset, length);
        insertUpdate(data);
        endEdits(de);
        insertOp = false;
    }
    
    void create(int length, DefaultStyledDocument$ElementSpec[] data, AbstractDocument$DefaultDocumentEvent de) {
        insertOp = true;
        beginEdits(offset, length);
        Element elem = root;
        int index = elem.getElementIndex(0);
        while (!elem.isLeaf()) {
            Element child = elem.getElement(index);
            push(elem, index);
            elem = child;
            index = elem.getElementIndex(0);
        }
        DefaultStyledDocument$ElementBuffer$ElemChanges ec = (DefaultStyledDocument$ElementBuffer$ElemChanges)(DefaultStyledDocument$ElementBuffer$ElemChanges)path.peek();
        Element child = ec.parent.getElement(ec.index);
        ec.added.addElement(this$0.createLeafElement(ec.parent, child.getAttributes(), this$0.getLength(), child.getEndOffset()));
        ec.removed.addElement(child);
        while (path.size() > 1) {
            pop();
        }
        int n = data.length;
        AttributeSet newAttrs = null;
        if (n > 0 && data[0].getType() == DefaultStyledDocument$ElementSpec.StartTagType) {
            newAttrs = data[0].getAttributes();
        }
        if (newAttrs == null) {
            newAttrs = SimpleAttributeSet.EMPTY;
        }
        MutableAttributeSet attr = (MutableAttributeSet)(MutableAttributeSet)root.getAttributes();
        de.addEdit(new DefaultStyledDocument$AttributeUndoableEdit(root, newAttrs, true));
        attr.removeAttributes(attr);
        attr.addAttributes(newAttrs);
        for (int i = 1; i < n; i++) {
            insertElement(data[i]);
        }
        while (path.size() != 0) {
            pop();
        }
        endEdits(de);
        insertOp = false;
    }
    
    public void remove(int offset, int length, AbstractDocument$DefaultDocumentEvent de) {
        beginEdits(offset, length);
        removeUpdate();
        endEdits(de);
    }
    
    public void change(int offset, int length, AbstractDocument$DefaultDocumentEvent de) {
        beginEdits(offset, length);
        changeUpdate();
        endEdits(de);
    }
    
    protected void insertUpdate(DefaultStyledDocument$ElementSpec[] data) {
        Element elem = root;
        int index = elem.getElementIndex(offset);
        while (!elem.isLeaf()) {
            Element child = elem.getElement(index);
            push(elem, (child.isLeaf() ? index : index + 1));
            elem = child;
            index = elem.getElementIndex(offset);
        }
        insertPath = new DefaultStyledDocument$ElementBuffer$ElemChanges[path.size()];
        path.copyInto(insertPath);
        createdFracture = false;
        int i;
        recreateLeafs = false;
        if (data[0].getType() == DefaultStyledDocument$ElementSpec.ContentType) {
            insertFirstContent(data);
            pos += data[0].getLength();
            i = 1;
        } else {
            fractureDeepestLeaf(data);
            i = 0;
        }
        int n = data.length;
        for (; i < n; i++) {
            insertElement(data[i]);
        }
        if (!createdFracture) fracture(-1);
        while (path.size() != 0) {
            pop();
        }
        if (offsetLastIndex && offsetLastIndexOnReplace) {
            insertPath[insertPath.length - 1].index++;
        }
        for (int counter = insertPath.length - 1; counter >= 0; counter--) {
            DefaultStyledDocument$ElementBuffer$ElemChanges change = insertPath[counter];
            if (change.parent == fracturedParent) change.added.addElement(fracturedChild);
            if ((change.added.size() > 0 || change.removed.size() > 0) && !changes.contains(change)) {
                changes.addElement(change);
            }
        }
        if (offset == 0 && fracturedParent != null && data[0].getType() == DefaultStyledDocument$ElementSpec.EndTagType) {
            int counter = 0;
            while (counter < data.length && data[counter].getType() == DefaultStyledDocument$ElementSpec.EndTagType) {
                counter++;
            }
            DefaultStyledDocument$ElementBuffer$ElemChanges change = insertPath[insertPath.length - counter - 1];
            change.removed.insertElementAt(change.parent.getElement(--change.index), 0);
        }
    }
    
    protected void removeUpdate() {
        removeElements(root, offset, offset + length);
    }
    
    protected void changeUpdate() {
        boolean didEnd = split(offset, length);
        if (!didEnd) {
            while (path.size() != 0) {
                pop();
            }
            split(offset + length, 0);
        }
        while (path.size() != 0) {
            pop();
        }
    }
    
    boolean split(int offs, int len) {
        boolean splitEnd = false;
        Element e = root;
        int index = e.getElementIndex(offs);
        while (!e.isLeaf()) {
            push(e, index);
            e = e.getElement(index);
            index = e.getElementIndex(offs);
        }
        DefaultStyledDocument$ElementBuffer$ElemChanges ec = (DefaultStyledDocument$ElementBuffer$ElemChanges)(DefaultStyledDocument$ElementBuffer$ElemChanges)path.peek();
        Element child = ec.parent.getElement(ec.index);
        if (child.getStartOffset() < offs && offs < child.getEndOffset()) {
            int index0 = ec.index;
            int index1 = index0;
            if (((offs + len) < ec.parent.getEndOffset()) && (len != 0)) {
                index1 = ec.parent.getElementIndex(offs + len);
                if (index1 == index0) {
                    ec.removed.addElement(child);
                    e = this$0.createLeafElement(ec.parent, child.getAttributes(), child.getStartOffset(), offs);
                    ec.added.addElement(e);
                    e = this$0.createLeafElement(ec.parent, child.getAttributes(), offs, offs + len);
                    ec.added.addElement(e);
                    e = this$0.createLeafElement(ec.parent, child.getAttributes(), offs + len, child.getEndOffset());
                    ec.added.addElement(e);
                    return true;
                } else {
                    child = ec.parent.getElement(index1);
                    if ((offs + len) == child.getStartOffset()) {
                        index1 = index0;
                    }
                }
                splitEnd = true;
            }
            pos = offs;
            child = ec.parent.getElement(index0);
            ec.removed.addElement(child);
            e = this$0.createLeafElement(ec.parent, child.getAttributes(), child.getStartOffset(), pos);
            ec.added.addElement(e);
            e = this$0.createLeafElement(ec.parent, child.getAttributes(), pos, child.getEndOffset());
            ec.added.addElement(e);
            for (int i = index0 + 1; i < index1; i++) {
                child = ec.parent.getElement(i);
                ec.removed.addElement(child);
                ec.added.addElement(child);
            }
            if (index1 != index0) {
                child = ec.parent.getElement(index1);
                pos = offs + len;
                ec.removed.addElement(child);
                e = this$0.createLeafElement(ec.parent, child.getAttributes(), child.getStartOffset(), pos);
                ec.added.addElement(e);
                e = this$0.createLeafElement(ec.parent, child.getAttributes(), pos, child.getEndOffset());
                ec.added.addElement(e);
            }
        }
        return splitEnd;
    }
    
    void endEdits(AbstractDocument$DefaultDocumentEvent de) {
        int n = changes.size();
        for (int i = 0; i < n; i++) {
            DefaultStyledDocument$ElementBuffer$ElemChanges ec = (DefaultStyledDocument$ElementBuffer$ElemChanges)(DefaultStyledDocument$ElementBuffer$ElemChanges)changes.elementAt(i);
            Element[] removed = new Element[ec.removed.size()];
            ec.removed.copyInto(removed);
            Element[] added = new Element[ec.added.size()];
            ec.added.copyInto(added);
            int index = ec.index;
            ((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)ec.parent).replace(index, removed.length, added);
            AbstractDocument$ElementEdit ee = new AbstractDocument$ElementEdit((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)ec.parent, index, removed, added);
            de.addEdit(ee);
        }
        changes.removeAllElements();
        path.removeAllElements();
    }
    
    void beginEdits(int offset, int length) {
        this.offset = offset;
        this.length = length;
        this.endOffset = offset + length;
        pos = offset;
        if (changes == null) {
            changes = new Vector();
        } else {
            changes.removeAllElements();
        }
        if (path == null) {
            path = new Stack();
        } else {
            path.removeAllElements();
        }
        fracturedParent = null;
        fracturedChild = null;
        offsetLastIndex = offsetLastIndexOnReplace = false;
    }
    
    void push(Element e, int index, boolean isFracture) {
        DefaultStyledDocument$ElementBuffer$ElemChanges ec = new DefaultStyledDocument$ElementBuffer$ElemChanges(this, e, index, isFracture);
        path.push(ec);
    }
    
    void push(Element e, int index) {
        push(e, index, false);
    }
    
    void pop() {
        DefaultStyledDocument$ElementBuffer$ElemChanges ec = (DefaultStyledDocument$ElementBuffer$ElemChanges)(DefaultStyledDocument$ElementBuffer$ElemChanges)path.peek();
        path.pop();
        if ((ec.added.size() > 0) || (ec.removed.size() > 0)) {
            changes.addElement(ec);
        } else if (!path.isEmpty()) {
            Element e = ec.parent;
            if (e.getElementCount() == 0) {
                ec = (DefaultStyledDocument$ElementBuffer$ElemChanges)(DefaultStyledDocument$ElementBuffer$ElemChanges)path.peek();
                ec.added.removeElement(e);
            }
        }
    }
    
    void advance(int n) {
        pos += n;
    }
    
    void insertElement(DefaultStyledDocument$ElementSpec es) {
        DefaultStyledDocument$ElementBuffer$ElemChanges ec = (DefaultStyledDocument$ElementBuffer$ElemChanges)(DefaultStyledDocument$ElementBuffer$ElemChanges)path.peek();
        switch (es.getType()) {
        case DefaultStyledDocument$ElementSpec.StartTagType: 
            switch (es.getDirection()) {
            case DefaultStyledDocument$ElementSpec.JoinNextDirection: 
                Element parent = ec.parent.getElement(ec.index);
                if (parent.isLeaf()) {
                    if ((ec.index + 1) < ec.parent.getElementCount()) parent = ec.parent.getElement(ec.index + 1); else throw new StateInvariantError("Join next to leaf");
                }
                push(parent, 0, true);
                break;
            
            case DefaultStyledDocument$ElementSpec.JoinFractureDirection: 
                if (!createdFracture) {
                    fracture(path.size() - 1);
                }
                if (!ec.isFracture) {
                    push(fracturedChild, 0, true);
                } else push(ec.parent.getElement(0), 0, true);
                break;
            
            default: 
                Element belem = this$0.createBranchElement(ec.parent, es.getAttributes());
                ec.added.addElement(belem);
                push(belem, 0);
                break;
            
            }
            break;
        
        case DefaultStyledDocument$ElementSpec.EndTagType: 
            pop();
            break;
        
        case DefaultStyledDocument$ElementSpec.ContentType: 
            int len = es.getLength();
            if (es.getDirection() != DefaultStyledDocument$ElementSpec.JoinNextDirection) {
                Element leaf = this$0.createLeafElement(ec.parent, es.getAttributes(), pos, pos + len);
                ec.added.addElement(leaf);
            } else {
                if (!ec.isFracture) {
                    Element first = null;
                    if (insertPath != null) {
                        for (int counter = insertPath.length - 1; counter >= 0; counter--) {
                            if (insertPath[counter] == ec) {
                                if (counter != (insertPath.length - 1)) first = ec.parent.getElement(ec.index);
                                break;
                            }
                        }
                    }
                    if (first == null) first = ec.parent.getElement(ec.index + 1);
                    Element leaf = this$0.createLeafElement(ec.parent, first.getAttributes(), pos, first.getEndOffset());
                    ec.added.addElement(leaf);
                    ec.removed.addElement(first);
                } else {
                    Element first = ec.parent.getElement(0);
                    Element leaf = this$0.createLeafElement(ec.parent, first.getAttributes(), pos, first.getEndOffset());
                    ec.added.addElement(leaf);
                    ec.removed.addElement(first);
                }
            }
            pos += len;
            break;
        
        }
    }
    
    boolean removeElements(Element elem, int rmOffs0, int rmOffs1) {
        if (!elem.isLeaf()) {
            int index0 = elem.getElementIndex(rmOffs0);
            int index1 = elem.getElementIndex(rmOffs1);
            push(elem, index0);
            DefaultStyledDocument$ElementBuffer$ElemChanges ec = (DefaultStyledDocument$ElementBuffer$ElemChanges)(DefaultStyledDocument$ElementBuffer$ElemChanges)path.peek();
            if (index0 == index1) {
                Element child0 = elem.getElement(index0);
                if (rmOffs0 <= child0.getStartOffset() && rmOffs1 >= child0.getEndOffset()) {
                    ec.removed.addElement(child0);
                } else if (removeElements(child0, rmOffs0, rmOffs1)) {
                    ec.removed.addElement(child0);
                }
            } else {
                Element child0 = elem.getElement(index0);
                Element child1 = elem.getElement(index1);
                boolean containsOffs1 = (rmOffs1 < elem.getEndOffset());
                if (containsOffs1 && canJoin(child0, child1)) {
                    for (int i = index0; i <= index1; i++) {
                        ec.removed.addElement(elem.getElement(i));
                    }
                    Element e = join(elem, child0, child1, rmOffs0, rmOffs1);
                    ec.added.addElement(e);
                } else {
                    int rmIndex0 = index0 + 1;
                    int rmIndex1 = index1 - 1;
                    if (child0.getStartOffset() == rmOffs0 || (index0 == 0 && child0.getStartOffset() > rmOffs0 && child0.getEndOffset() <= rmOffs1)) {
                        child0 = null;
                        rmIndex0 = index0;
                    }
                    if (!containsOffs1) {
                        child1 = null;
                        rmIndex1++;
                    } else if (child1.getStartOffset() == rmOffs1) {
                        child1 = null;
                    }
                    if (rmIndex0 <= rmIndex1) {
                        ec.index = rmIndex0;
                    }
                    for (int i = rmIndex0; i <= rmIndex1; i++) {
                        ec.removed.addElement(elem.getElement(i));
                    }
                    if (child0 != null) {
                        if (removeElements(child0, rmOffs0, rmOffs1)) {
                            ec.removed.insertElementAt(child0, 0);
                            ec.index = index0;
                        }
                    }
                    if (child1 != null) {
                        if (removeElements(child1, rmOffs0, rmOffs1)) {
                            ec.removed.addElement(child1);
                        }
                    }
                }
            }
            pop();
            if (elem.getElementCount() == (ec.removed.size() - ec.added.size())) {
                return true;
            }
        }
        return false;
    }
    
    boolean canJoin(Element e0, Element e1) {
        if ((e0 == null) || (e1 == null)) {
            return false;
        }
        boolean leaf0 = e0.isLeaf();
        boolean leaf1 = e1.isLeaf();
        if (leaf0 != leaf1) {
            return false;
        }
        if (leaf0) {
            return e0.getAttributes().isEqual(e1.getAttributes());
        }
        String name0 = e0.getName();
        String name1 = e1.getName();
        if (name0 != null) {
            return name0.equals(name1);
        }
        if (name1 != null) {
            return name1.equals(name0);
        }
        return true;
    }
    
    Element join(Element p, Element left, Element right, int rmOffs0, int rmOffs1) {
        if (left.isLeaf() && right.isLeaf()) {
            return this$0.createLeafElement(p, left.getAttributes(), left.getStartOffset(), right.getEndOffset());
        } else if ((!left.isLeaf()) && (!right.isLeaf())) {
            Element to = this$0.createBranchElement(p, left.getAttributes());
            int ljIndex = left.getElementIndex(rmOffs0);
            int rjIndex = right.getElementIndex(rmOffs1);
            Element lj = left.getElement(ljIndex);
            if (lj.getStartOffset() >= rmOffs0) {
                lj = null;
            }
            Element rj = right.getElement(rjIndex);
            if (rj.getStartOffset() == rmOffs1) {
                rj = null;
            }
            Vector children = new Vector();
            for (int i = 0; i < ljIndex; i++) {
                children.addElement(clone(to, left.getElement(i)));
            }
            if (canJoin(lj, rj)) {
                Element e = join(to, lj, rj, rmOffs0, rmOffs1);
                children.addElement(e);
            } else {
                if (lj != null) {
                    children.addElement(cloneAsNecessary(to, lj, rmOffs0, rmOffs1));
                }
                if (rj != null) {
                    children.addElement(cloneAsNecessary(to, rj, rmOffs0, rmOffs1));
                }
            }
            int n = right.getElementCount();
            for (int i = (rj == null) ? rjIndex : rjIndex + 1; i < n; i++) {
                children.addElement(clone(to, right.getElement(i)));
            }
            Element[] c = new Element[children.size()];
            children.copyInto(c);
            ((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)to).replace(0, 0, c);
            return to;
        } else {
            throw new StateInvariantError("No support to join leaf element with non-leaf element");
        }
    }
    
    public Element clone(Element parent, Element clonee) {
        if (clonee.isLeaf()) {
            return this$0.createLeafElement(parent, clonee.getAttributes(), clonee.getStartOffset(), clonee.getEndOffset());
        }
        Element e = this$0.createBranchElement(parent, clonee.getAttributes());
        int n = clonee.getElementCount();
        Element[] children = new Element[n];
        for (int i = 0; i < n; i++) {
            children[i] = clone(e, clonee.getElement(i));
        }
        ((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)e).replace(0, 0, children);
        return e;
    }
    
    Element cloneAsNecessary(Element parent, Element clonee, int rmOffs0, int rmOffs1) {
        if (clonee.isLeaf()) {
            return this$0.createLeafElement(parent, clonee.getAttributes(), clonee.getStartOffset(), clonee.getEndOffset());
        }
        Element e = this$0.createBranchElement(parent, clonee.getAttributes());
        int n = clonee.getElementCount();
        ArrayList childrenList = new ArrayList(n);
        for (int i = 0; i < n; i++) {
            Element elem = clonee.getElement(i);
            if (elem.getStartOffset() < rmOffs0 || elem.getEndOffset() > rmOffs1) {
                childrenList.add(cloneAsNecessary(e, elem, rmOffs0, rmOffs1));
            }
        }
        Element[] children = new Element[childrenList.size()];
        children = (Element[])(Element[])childrenList.toArray(children);
        ((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)e).replace(0, 0, children);
        return e;
    }
    
    void fracture(int depth) {
        int cLength = insertPath.length;
        int lastIndex = -1;
        boolean needRecreate = recreateLeafs;
        DefaultStyledDocument$ElementBuffer$ElemChanges lastChange = insertPath[cLength - 1];
        boolean childAltered = ((lastChange.index + 1) < lastChange.parent.getElementCount());
        int deepestAlteredIndex = (needRecreate) ? cLength : -1;
        int lastAlteredIndex = cLength - 1;
        createdFracture = true;
        for (int counter = cLength - 2; counter >= 0; counter--) {
            DefaultStyledDocument$ElementBuffer$ElemChanges change = insertPath[counter];
            if (change.added.size() > 0 || counter == depth) {
                lastIndex = counter;
                if (!needRecreate && childAltered) {
                    needRecreate = true;
                    if (deepestAlteredIndex == -1) deepestAlteredIndex = lastAlteredIndex + 1;
                }
            }
            if (!childAltered && change.index < change.parent.getElementCount()) {
                childAltered = true;
                lastAlteredIndex = counter;
            }
        }
        if (needRecreate) {
            if (lastIndex == -1) lastIndex = cLength - 1;
            fractureFrom(insertPath, lastIndex, deepestAlteredIndex);
        }
    }
    
    void fractureFrom(DefaultStyledDocument$ElementBuffer$ElemChanges[] changed, int startIndex, int endFractureIndex) {
        DefaultStyledDocument$ElementBuffer$ElemChanges change = changed[startIndex];
        Element child;
        Element newChild;
        int changeLength = changed.length;
        if ((startIndex + 1) == changeLength) child = change.parent.getElement(change.index); else child = change.parent.getElement(change.index - 1);
        if (child.isLeaf()) {
            newChild = this$0.createLeafElement(change.parent, child.getAttributes(), Math.max(endOffset, child.getStartOffset()), child.getEndOffset());
        } else {
            newChild = this$0.createBranchElement(change.parent, child.getAttributes());
        }
        fracturedParent = change.parent;
        fracturedChild = newChild;
        Element parent = newChild;
        while (++startIndex < endFractureIndex) {
            boolean isEnd = ((startIndex + 1) == endFractureIndex);
            boolean isEndLeaf = ((startIndex + 1) == changeLength);
            change = changed[startIndex];
            if (isEnd) {
                if (offsetLastIndex || !isEndLeaf) child = null; else child = change.parent.getElement(change.index);
            } else {
                child = change.parent.getElement(change.index - 1);
            }
            if (child != null) {
                if (child.isLeaf()) {
                    newChild = this$0.createLeafElement(parent, child.getAttributes(), Math.max(endOffset, child.getStartOffset()), child.getEndOffset());
                } else {
                    newChild = this$0.createBranchElement(parent, child.getAttributes());
                }
            } else newChild = null;
            int kidsToMove = change.parent.getElementCount() - change.index;
            Element[] kids;
            int moveStartIndex;
            int kidStartIndex = 1;
            if (newChild == null) {
                if (isEndLeaf) {
                    kidsToMove--;
                    moveStartIndex = change.index + 1;
                } else {
                    moveStartIndex = change.index;
                }
                kidStartIndex = 0;
                kids = new Element[kidsToMove];
            } else {
                if (!isEnd) {
                    kidsToMove++;
                    moveStartIndex = change.index;
                } else {
                    moveStartIndex = change.index + 1;
                }
                kids = new Element[kidsToMove];
                kids[0] = newChild;
            }
            for (int counter = kidStartIndex; counter < kidsToMove; counter++) {
                Element toMove = change.parent.getElement(moveStartIndex++);
                kids[counter] = recreateFracturedElement(parent, toMove);
                change.removed.addElement(toMove);
            }
            ((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)parent).replace(0, 0, kids);
            parent = newChild;
        }
    }
    
    Element recreateFracturedElement(Element parent, Element toDuplicate) {
        if (toDuplicate.isLeaf()) {
            return this$0.createLeafElement(parent, toDuplicate.getAttributes(), Math.max(toDuplicate.getStartOffset(), endOffset), toDuplicate.getEndOffset());
        }
        Element newParent = this$0.createBranchElement(parent, toDuplicate.getAttributes());
        int childCount = toDuplicate.getElementCount();
        Element[] newKids = new Element[childCount];
        for (int counter = 0; counter < childCount; counter++) {
            newKids[counter] = recreateFracturedElement(newParent, toDuplicate.getElement(counter));
        }
        ((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)newParent).replace(0, 0, newKids);
        return newParent;
    }
    
    void fractureDeepestLeaf(DefaultStyledDocument$ElementSpec[] specs) {
        DefaultStyledDocument$ElementBuffer$ElemChanges ec = (DefaultStyledDocument$ElementBuffer$ElemChanges)(DefaultStyledDocument$ElementBuffer$ElemChanges)path.peek();
        Element child = ec.parent.getElement(ec.index);
        if (offset != 0) {
            Element newChild = this$0.createLeafElement(ec.parent, child.getAttributes(), child.getStartOffset(), offset);
            ec.added.addElement(newChild);
        }
        ec.removed.addElement(child);
        if (child.getEndOffset() != endOffset) recreateLeafs = true; else offsetLastIndex = true;
    }
    
    void insertFirstContent(DefaultStyledDocument$ElementSpec[] specs) {
        DefaultStyledDocument$ElementSpec firstSpec = specs[0];
        DefaultStyledDocument$ElementBuffer$ElemChanges ec = (DefaultStyledDocument$ElementBuffer$ElemChanges)(DefaultStyledDocument$ElementBuffer$ElemChanges)path.peek();
        Element child = ec.parent.getElement(ec.index);
        int firstEndOffset = offset + firstSpec.getLength();
        boolean isOnlyContent = (specs.length == 1);
        switch (firstSpec.getDirection()) {
        case DefaultStyledDocument$ElementSpec.JoinPreviousDirection: 
            if (child.getEndOffset() != firstEndOffset && !isOnlyContent) {
                Element newE = this$0.createLeafElement(ec.parent, child.getAttributes(), child.getStartOffset(), firstEndOffset);
                ec.added.addElement(newE);
                ec.removed.addElement(child);
                if (child.getEndOffset() != endOffset) recreateLeafs = true; else offsetLastIndex = true;
            } else {
                offsetLastIndex = true;
                offsetLastIndexOnReplace = true;
            }
            break;
        
        case DefaultStyledDocument$ElementSpec.JoinNextDirection: 
            if (offset != 0) {
                Element newE = this$0.createLeafElement(ec.parent, child.getAttributes(), child.getStartOffset(), offset);
                ec.added.addElement(newE);
                Element nextChild = ec.parent.getElement(ec.index + 1);
                if (isOnlyContent) newE = this$0.createLeafElement(ec.parent, nextChild.getAttributes(), offset, nextChild.getEndOffset()); else newE = this$0.createLeafElement(ec.parent, nextChild.getAttributes(), offset, firstEndOffset);
                ec.added.addElement(newE);
                ec.removed.addElement(child);
                ec.removed.addElement(nextChild);
            }
            break;
        
        default: 
            if (child.getStartOffset() != offset) {
                Element newE = this$0.createLeafElement(ec.parent, child.getAttributes(), child.getStartOffset(), offset);
                ec.added.addElement(newE);
            }
            ec.removed.addElement(child);
            Element newE = this$0.createLeafElement(ec.parent, firstSpec.getAttributes(), offset, firstEndOffset);
            ec.added.addElement(newE);
            if (child.getEndOffset() != endOffset) {
                recreateLeafs = true;
            } else {
                offsetLastIndex = true;
            }
            break;
        
        }
    }
    Element root;
    transient int pos;
    transient int offset;
    transient int length;
    transient int endOffset;
    transient Vector changes;
    transient Stack path;
    transient boolean insertOp;
    transient boolean recreateLeafs;
    transient DefaultStyledDocument$ElementBuffer$ElemChanges[] insertPath;
    transient boolean createdFracture;
    transient Element fracturedParent;
    transient Element fracturedChild;
    transient boolean offsetLastIndex;
    transient boolean offsetLastIndexOnReplace;
    {
    }
}
