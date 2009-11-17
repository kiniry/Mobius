package javax.swing.tree;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.*;
import java.util.EventObject;
import java.util.Vector;

public class DefaultTreeCellEditor implements ActionListener, TreeCellEditor, TreeSelectionListener {
    protected TreeCellEditor realEditor;
    protected DefaultTreeCellRenderer renderer;
    protected Container editingContainer;
    protected transient Component editingComponent;
    protected boolean canEdit;
    protected transient int offset;
    protected transient JTree tree;
    protected transient TreePath lastPath;
    protected transient Timer timer;
    protected transient int lastRow;
    protected Color borderSelectionColor;
    protected transient Icon editingIcon;
    protected Font font;
    
    public DefaultTreeCellEditor(JTree tree, DefaultTreeCellRenderer renderer) {
        this(tree, renderer, null);
    }
    
    public DefaultTreeCellEditor(JTree tree, DefaultTreeCellRenderer renderer, TreeCellEditor editor) {
        
        this.renderer = renderer;
        realEditor = editor;
        if (realEditor == null) realEditor = createTreeCellEditor();
        editingContainer = createContainer();
        setTree(tree);
        setBorderSelectionColor(UIManager.getColor("Tree.editorBorderSelectionColor"));
    }
    
    public void setBorderSelectionColor(Color newColor) {
        borderSelectionColor = newColor;
    }
    
    public Color getBorderSelectionColor() {
        return borderSelectionColor;
    }
    
    public void setFont(Font font) {
        this.font = font;
    }
    
    public Font getFont() {
        return font;
    }
    
    public Component getTreeCellEditorComponent(JTree tree, Object value, boolean isSelected, boolean expanded, boolean leaf, int row) {
        setTree(tree);
        lastRow = row;
        determineOffset(tree, value, isSelected, expanded, leaf, row);
        if (editingComponent != null) {
            editingContainer.remove(editingComponent);
        }
        editingComponent = realEditor.getTreeCellEditorComponent(tree, value, isSelected, expanded, leaf, row);
        TreePath newPath = tree.getPathForRow(row);
        canEdit = (lastPath != null && newPath != null && lastPath.equals(newPath));
        Font font = getFont();
        if (font == null) {
            if (renderer != null) font = renderer.getFont();
            if (font == null) font = tree.getFont();
        }
        editingContainer.setFont(font);
        prepareForEditing();
        return editingContainer;
    }
    
    public Object getCellEditorValue() {
        return realEditor.getCellEditorValue();
    }
    
    public boolean isCellEditable(EventObject event) {
        boolean retValue = false;
        boolean editable = false;
        if (event != null) {
            if (event.getSource() instanceof JTree) {
                setTree((JTree)(JTree)event.getSource());
                if (event instanceof MouseEvent) {
                    TreePath path = tree.getPathForLocation(((MouseEvent)(MouseEvent)event).getX(), ((MouseEvent)(MouseEvent)event).getY());
                    editable = (lastPath != null && path != null && lastPath.equals(path));
                    if (path != null) {
                        lastRow = tree.getRowForPath(path);
                        Object value = path.getLastPathComponent();
                        boolean isSelected = tree.isRowSelected(lastRow);
                        boolean expanded = tree.isExpanded(path);
                        TreeModel treeModel = tree.getModel();
                        boolean leaf = treeModel.isLeaf(value);
                        determineOffset(tree, value, isSelected, expanded, leaf, lastRow);
                    }
                }
            }
        }
        if (!realEditor.isCellEditable(event)) return false;
        if (canEditImmediately(event)) retValue = true; else if (editable && shouldStartEditingTimer(event)) {
            startEditingTimer();
        } else if (timer != null && timer.isRunning()) timer.stop();
        if (retValue) prepareForEditing();
        return retValue;
    }
    
    public boolean shouldSelectCell(EventObject event) {
        return realEditor.shouldSelectCell(event);
    }
    
    public boolean stopCellEditing() {
        if (realEditor.stopCellEditing()) {
            cleanupAfterEditing();
            return true;
        }
        return false;
    }
    
    public void cancelCellEditing() {
        realEditor.cancelCellEditing();
        cleanupAfterEditing();
    }
    
    public void addCellEditorListener(CellEditorListener l) {
        realEditor.addCellEditorListener(l);
    }
    
    public void removeCellEditorListener(CellEditorListener l) {
        realEditor.removeCellEditorListener(l);
    }
    
    public CellEditorListener[] getCellEditorListeners() {
        return ((DefaultCellEditor)(DefaultCellEditor)realEditor).getCellEditorListeners();
    }
    
    public void valueChanged(TreeSelectionEvent e) {
        if (tree != null) {
            if (tree.getSelectionCount() == 1) lastPath = tree.getSelectionPath(); else lastPath = null;
        }
        if (timer != null) {
            timer.stop();
        }
    }
    
    public void actionPerformed(ActionEvent e) {
        if (tree != null && lastPath != null) {
            tree.startEditingAtPath(lastPath);
        }
    }
    
    protected void setTree(JTree newTree) {
        if (tree != newTree) {
            if (tree != null) tree.removeTreeSelectionListener(this);
            tree = newTree;
            if (tree != null) tree.addTreeSelectionListener(this);
            if (timer != null) {
                timer.stop();
            }
        }
    }
    
    protected boolean shouldStartEditingTimer(EventObject event) {
        if ((event instanceof MouseEvent) && SwingUtilities.isLeftMouseButton((MouseEvent)(MouseEvent)event)) {
            MouseEvent me = (MouseEvent)(MouseEvent)event;
            return (me.getClickCount() == 1 && inHitRegion(me.getX(), me.getY()));
        }
        return false;
    }
    
    protected void startEditingTimer() {
        if (timer == null) {
            timer = new Timer(1200, this);
            timer.setRepeats(false);
        }
        timer.start();
    }
    
    protected boolean canEditImmediately(EventObject event) {
        if ((event instanceof MouseEvent) && SwingUtilities.isLeftMouseButton((MouseEvent)(MouseEvent)event)) {
            MouseEvent me = (MouseEvent)(MouseEvent)event;
            return ((me.getClickCount() > 2) && inHitRegion(me.getX(), me.getY()));
        }
        return (event == null);
    }
    
    protected boolean inHitRegion(int x, int y) {
        if (lastRow != -1 && tree != null) {
            Rectangle bounds = tree.getRowBounds(lastRow);
            ComponentOrientation treeOrientation = tree.getComponentOrientation();
            if (treeOrientation.isLeftToRight()) {
                if (bounds != null && x <= (bounds.x + offset) && offset < (bounds.width - 5)) {
                    return false;
                }
            } else if (bounds != null && (x >= (bounds.x + bounds.width - offset + 5) || x <= (bounds.x + 5)) && offset < (bounds.width - 5)) {
                return false;
            }
        }
        return true;
    }
    
    protected void determineOffset(JTree tree, Object value, boolean isSelected, boolean expanded, boolean leaf, int row) {
        if (renderer != null) {
            if (leaf) editingIcon = renderer.getLeafIcon(); else if (expanded) editingIcon = renderer.getOpenIcon(); else editingIcon = renderer.getClosedIcon();
            if (editingIcon != null) offset = renderer.getIconTextGap() + editingIcon.getIconWidth(); else offset = renderer.getIconTextGap();
        } else {
            editingIcon = null;
            offset = 0;
        }
    }
    
    protected void prepareForEditing() {
        if (editingComponent != null) {
            editingContainer.add(editingComponent);
        }
    }
    
    protected Container createContainer() {
        return new DefaultTreeCellEditor$EditorContainer(this);
    }
    
    protected TreeCellEditor createTreeCellEditor() {
        Border aBorder = UIManager.getBorder("Tree.editorBorder");
        DefaultCellEditor editor = new DefaultTreeCellEditor$1(this, new DefaultTreeCellEditor$DefaultTextField(this, aBorder));
        editor.setClickCountToStart(1);
        return editor;
    }
    
    private void cleanupAfterEditing() {
        if (editingComponent != null) {
            editingContainer.remove(editingComponent);
        }
        editingComponent = null;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        Vector values = new Vector();
        s.defaultWriteObject();
        if (realEditor != null && realEditor instanceof Serializable) {
            values.addElement("realEditor");
            values.addElement(realEditor);
        }
        s.writeObject(values);
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        Vector values = (Vector)(Vector)s.readObject();
        int indexCounter = 0;
        int maxCounter = values.size();
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("realEditor")) {
            realEditor = (TreeCellEditor)(TreeCellEditor)values.elementAt(++indexCounter);
            indexCounter++;
        }
    }
    {
    }
    {
    }
}
