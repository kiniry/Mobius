package javax.swing.tree;

import java.beans.PropertyChangeListener;
import java.io.*;
import java.util.BitSet;
import java.util.Enumeration;
import java.util.EventListener;
import java.util.Hashtable;
import java.util.Vector;
import javax.swing.event.*;
import javax.swing.DefaultListSelectionModel;

public class DefaultTreeSelectionModel extends Object implements Cloneable, Serializable, TreeSelectionModel {
    public static final String SELECTION_MODE_PROPERTY = "selectionMode";
    protected SwingPropertyChangeSupport changeSupport;
    protected TreePath[] selection;
    protected EventListenerList listenerList = new EventListenerList();
    protected transient RowMapper rowMapper;
    protected DefaultListSelectionModel listSelectionModel;
    protected int selectionMode;
    protected TreePath leadPath;
    protected int leadIndex;
    protected int leadRow;
    private Hashtable uniquePaths;
    private Hashtable lastPaths;
    private TreePath[] tempPaths;
    
    public DefaultTreeSelectionModel() {
        
        listSelectionModel = new DefaultListSelectionModel();
        selectionMode = DISCONTIGUOUS_TREE_SELECTION;
        leadIndex = leadRow = -1;
        uniquePaths = new Hashtable();
        lastPaths = new Hashtable();
        tempPaths = new TreePath[1];
    }
    
    public void setRowMapper(RowMapper newMapper) {
        rowMapper = newMapper;
        resetRowSelection();
    }
    
    public RowMapper getRowMapper() {
        return rowMapper;
    }
    
    public void setSelectionMode(int mode) {
        int oldMode = selectionMode;
        selectionMode = mode;
        if (selectionMode != TreeSelectionModel.SINGLE_TREE_SELECTION && selectionMode != TreeSelectionModel.CONTIGUOUS_TREE_SELECTION && selectionMode != TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION) selectionMode = TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION;
        if (oldMode != selectionMode && changeSupport != null) changeSupport.firePropertyChange(SELECTION_MODE_PROPERTY, new Integer(oldMode), new Integer(selectionMode));
    }
    
    public int getSelectionMode() {
        return selectionMode;
    }
    
    public void setSelectionPath(TreePath path) {
        if (path == null) setSelectionPaths(null); else {
            TreePath[] newPaths = new TreePath[1];
            newPaths[0] = path;
            setSelectionPaths(newPaths);
        }
    }
    
    public void setSelectionPaths(TreePath[] pPaths) {
        int newCount;
        int newCounter;
        int oldCount;
        int oldCounter;
        TreePath[] paths = pPaths;
        if (paths == null) newCount = 0; else newCount = paths.length;
        if (selection == null) oldCount = 0; else oldCount = selection.length;
        if ((newCount + oldCount) != 0) {
            if (selectionMode == TreeSelectionModel.SINGLE_TREE_SELECTION) {
                if (newCount > 1) {
                    paths = new TreePath[1];
                    paths[0] = pPaths[0];
                    newCount = 1;
                }
            } else if (selectionMode == TreeSelectionModel.CONTIGUOUS_TREE_SELECTION) {
                if (newCount > 0 && !arePathsContiguous(paths)) {
                    paths = new TreePath[1];
                    paths[0] = pPaths[0];
                    newCount = 1;
                }
            }
            int validCount = 0;
            TreePath beginLeadPath = leadPath;
            Vector cPaths = new Vector(newCount + oldCount);
            lastPaths.clear();
            leadPath = null;
            for (newCounter = 0; newCounter < newCount; newCounter++) {
                if (paths[newCounter] != null && lastPaths.get(paths[newCounter]) == null) {
                    validCount++;
                    lastPaths.put(paths[newCounter], Boolean.TRUE);
                    if (uniquePaths.get(paths[newCounter]) == null) {
                        cPaths.addElement(new PathPlaceHolder(paths[newCounter], true));
                    }
                    leadPath = paths[newCounter];
                }
            }
            TreePath[] newSelection;
            if (validCount == 0) {
                newSelection = null;
            } else if (validCount != newCount) {
                Enumeration keys = lastPaths.keys();
                newSelection = new TreePath[validCount];
                validCount = 0;
                while (keys.hasMoreElements()) {
                    newSelection[validCount++] = (TreePath)(TreePath)keys.nextElement();
                }
            } else {
                newSelection = new TreePath[paths.length];
                System.arraycopy(paths, 0, newSelection, 0, paths.length);
            }
            for (oldCounter = 0; oldCounter < oldCount; oldCounter++) if (selection[oldCounter] != null && lastPaths.get(selection[oldCounter]) == null) cPaths.addElement(new PathPlaceHolder(selection[oldCounter], false));
            selection = newSelection;
            Hashtable tempHT = uniquePaths;
            uniquePaths = lastPaths;
            lastPaths = tempHT;
            lastPaths.clear();
            if (selection != null) insureUniqueness();
            updateLeadIndex();
            resetRowSelection();
            if (cPaths.size() > 0) notifyPathChange(cPaths, beginLeadPath);
        }
    }
    
    public void addSelectionPath(TreePath path) {
        if (path != null) {
            TreePath[] toAdd = new TreePath[1];
            toAdd[0] = path;
            addSelectionPaths(toAdd);
        }
    }
    
    public void addSelectionPaths(TreePath[] paths) {
        int newPathLength = ((paths == null) ? 0 : paths.length);
        if (newPathLength > 0) {
            if (selectionMode == TreeSelectionModel.SINGLE_TREE_SELECTION) {
                setSelectionPaths(paths);
            } else if (selectionMode == TreeSelectionModel.CONTIGUOUS_TREE_SELECTION && !canPathsBeAdded(paths)) {
                if (arePathsContiguous(paths)) {
                    setSelectionPaths(paths);
                } else {
                    TreePath[] newPaths = new TreePath[1];
                    newPaths[0] = paths[0];
                    setSelectionPaths(newPaths);
                }
            } else {
                int counter;
                int validCount;
                int oldCount;
                TreePath beginLeadPath = leadPath;
                Vector cPaths = null;
                if (selection == null) oldCount = 0; else oldCount = selection.length;
                lastPaths.clear();
                for (counter = 0, validCount = 0; counter < newPathLength; counter++) {
                    if (paths[counter] != null) {
                        if (uniquePaths.get(paths[counter]) == null) {
                            validCount++;
                            if (cPaths == null) cPaths = new Vector();
                            cPaths.addElement(new PathPlaceHolder(paths[counter], true));
                            uniquePaths.put(paths[counter], Boolean.TRUE);
                            lastPaths.put(paths[counter], Boolean.TRUE);
                        }
                        leadPath = paths[counter];
                    }
                }
                if (leadPath == null) {
                    leadPath = beginLeadPath;
                }
                if (validCount > 0) {
                    TreePath[] newSelection = new TreePath[oldCount + validCount];
                    if (oldCount > 0) System.arraycopy(selection, 0, newSelection, 0, oldCount);
                    if (validCount != paths.length) {
                        Enumeration newPaths = lastPaths.keys();
                        counter = oldCount;
                        while (newPaths.hasMoreElements()) {
                            newSelection[counter++] = (TreePath)(TreePath)newPaths.nextElement();
                        }
                    } else {
                        System.arraycopy(paths, 0, newSelection, oldCount, validCount);
                    }
                    selection = newSelection;
                    insureUniqueness();
                    updateLeadIndex();
                    resetRowSelection();
                    notifyPathChange(cPaths, beginLeadPath);
                } else leadPath = beginLeadPath;
                lastPaths.clear();
            }
        }
    }
    
    public void removeSelectionPath(TreePath path) {
        if (path != null) {
            TreePath[] rPath = new TreePath[1];
            rPath[0] = path;
            removeSelectionPaths(rPath);
        }
    }
    
    public void removeSelectionPaths(TreePath[] paths) {
        if (paths != null && selection != null && paths.length > 0) {
            if (!canPathsBeRemoved(paths)) {
                clearSelection();
            } else {
                Vector pathsToRemove = null;
                for (int removeCounter = paths.length - 1; removeCounter >= 0; removeCounter--) {
                    if (paths[removeCounter] != null) {
                        if (uniquePaths.get(paths[removeCounter]) != null) {
                            if (pathsToRemove == null) pathsToRemove = new Vector(paths.length);
                            uniquePaths.remove(paths[removeCounter]);
                            pathsToRemove.addElement(new PathPlaceHolder(paths[removeCounter], false));
                        }
                    }
                }
                if (pathsToRemove != null) {
                    int removeCount = pathsToRemove.size();
                    TreePath beginLeadPath = leadPath;
                    if (removeCount == selection.length) {
                        selection = null;
                    } else {
                        Enumeration pEnum = uniquePaths.keys();
                        int validCount = 0;
                        selection = new TreePath[selection.length - removeCount];
                        while (pEnum.hasMoreElements()) {
                            selection[validCount++] = (TreePath)(TreePath)pEnum.nextElement();
                        }
                    }
                    if (leadPath != null && uniquePaths.get(leadPath) == null) {
                        if (selection != null) {
                            leadPath = selection[selection.length - 1];
                        } else {
                            leadPath = null;
                        }
                    } else if (selection != null) {
                        leadPath = selection[selection.length - 1];
                    } else {
                        leadPath = null;
                    }
                    updateLeadIndex();
                    resetRowSelection();
                    notifyPathChange(pathsToRemove, beginLeadPath);
                }
            }
        }
    }
    
    public TreePath getSelectionPath() {
        if (selection != null) return selection[0];
        return null;
    }
    
    public TreePath[] getSelectionPaths() {
        if (selection != null) {
            int pathSize = selection.length;
            TreePath[] result = new TreePath[pathSize];
            System.arraycopy(selection, 0, result, 0, pathSize);
            return result;
        }
        return null;
    }
    
    public int getSelectionCount() {
        return (selection == null) ? 0 : selection.length;
    }
    
    public boolean isPathSelected(TreePath path) {
        return (path != null) ? (uniquePaths.get(path) != null) : false;
    }
    
    public boolean isSelectionEmpty() {
        return (selection == null);
    }
    
    public void clearSelection() {
        if (selection != null) {
            int selSize = selection.length;
            boolean[] newness = new boolean[selSize];
            for (int counter = 0; counter < selSize; counter++) newness[counter] = false;
            TreeSelectionEvent event = new TreeSelectionEvent(this, selection, newness, leadPath, null);
            leadPath = null;
            leadIndex = leadRow = -1;
            uniquePaths.clear();
            selection = null;
            resetRowSelection();
            fireValueChanged(event);
        }
    }
    
    public void addTreeSelectionListener(TreeSelectionListener x) {
        listenerList.add(TreeSelectionListener.class, x);
    }
    
    public void removeTreeSelectionListener(TreeSelectionListener x) {
        listenerList.remove(TreeSelectionListener.class, x);
    }
    
    public TreeSelectionListener[] getTreeSelectionListeners() {
        return (TreeSelectionListener[])(TreeSelectionListener[])listenerList.getListeners(TreeSelectionListener.class);
    }
    
    protected void fireValueChanged(TreeSelectionEvent e) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == TreeSelectionListener.class) {
                ((TreeSelectionListener)(TreeSelectionListener)listeners[i + 1]).valueChanged(e);
            }
        }
    }
    
    public EventListener[] getListeners(Class listenerType) {
        return listenerList.getListeners(listenerType);
    }
    
    public int[] getSelectionRows() {
        if (rowMapper != null && selection != null) {
            int[] rows = rowMapper.getRowsForPaths(selection);
            if (rows != null) {
                int invisCount = 0;
                for (int counter = rows.length - 1; counter >= 0; counter--) {
                    if (rows[counter] == -1) {
                        invisCount++;
                    }
                }
                if (invisCount > 0) {
                    if (invisCount == rows.length) {
                        rows = null;
                    } else {
                        int[] tempRows = new int[rows.length - invisCount];
                        for (int counter = rows.length - 1, visCounter = 0; counter >= 0; counter--) {
                            if (rows[counter] != -1) {
                                tempRows[visCounter++] = rows[counter];
                            }
                        }
                        rows = tempRows;
                    }
                }
            }
            return rows;
        }
        return null;
    }
    
    public int getMinSelectionRow() {
        return listSelectionModel.getMinSelectionIndex();
    }
    
    public int getMaxSelectionRow() {
        return listSelectionModel.getMaxSelectionIndex();
    }
    
    public boolean isRowSelected(int row) {
        return listSelectionModel.isSelectedIndex(row);
    }
    
    public void resetRowSelection() {
        listSelectionModel.clearSelection();
        if (selection != null && rowMapper != null) {
            int aRow;
            int validCount = 0;
            int[] rows = rowMapper.getRowsForPaths(selection);
            for (int counter = 0, maxCounter = selection.length; counter < maxCounter; counter++) {
                aRow = rows[counter];
                if (aRow != -1) {
                    listSelectionModel.addSelectionInterval(aRow, aRow);
                }
            }
            if (leadIndex != -1 && rows != null) {
                leadRow = rows[leadIndex];
            } else if (leadPath != null) {
                tempPaths[0] = leadPath;
                rows = rowMapper.getRowsForPaths(tempPaths);
                leadRow = (rows != null) ? rows[0] : -1;
            } else {
                leadRow = -1;
            }
            insureRowContinuity();
        } else leadRow = -1;
    }
    
    public int getLeadSelectionRow() {
        return leadRow;
    }
    
    public TreePath getLeadSelectionPath() {
        return leadPath;
    }
    
    public synchronized void addPropertyChangeListener(PropertyChangeListener listener) {
        if (changeSupport == null) {
            changeSupport = new SwingPropertyChangeSupport(this);
        }
        changeSupport.addPropertyChangeListener(listener);
    }
    
    public synchronized void removePropertyChangeListener(PropertyChangeListener listener) {
        if (changeSupport == null) {
            return;
        }
        changeSupport.removePropertyChangeListener(listener);
    }
    
    public PropertyChangeListener[] getPropertyChangeListeners() {
        if (changeSupport == null) {
            return new PropertyChangeListener[0];
        }
        return changeSupport.getPropertyChangeListeners();
    }
    
    protected void insureRowContinuity() {
        if (selectionMode == TreeSelectionModel.CONTIGUOUS_TREE_SELECTION && selection != null && rowMapper != null) {
            DefaultListSelectionModel lModel = listSelectionModel;
            int min = lModel.getMinSelectionIndex();
            if (min != -1) {
                for (int counter = min, maxCounter = lModel.getMaxSelectionIndex(); counter <= maxCounter; counter++) {
                    if (!lModel.isSelectedIndex(counter)) {
                        if (counter == min) {
                            clearSelection();
                        } else {
                            TreePath[] newSel = new TreePath[counter - min];
                            int[] selectionIndex = rowMapper.getRowsForPaths(selection);
                            for (int i = 0; i < selectionIndex.length; i++) {
                                if (selectionIndex[i] < counter) {
                                    newSel[selectionIndex[i] - min] = selection[i];
                                }
                            }
                            setSelectionPaths(newSel);
                            break;
                        }
                    }
                }
            }
        } else if (selectionMode == TreeSelectionModel.SINGLE_TREE_SELECTION && selection != null && selection.length > 1) {
            setSelectionPath(selection[0]);
        }
    }
    
    protected boolean arePathsContiguous(TreePath[] paths) {
        if (rowMapper == null || paths.length < 2) return true; else {
            BitSet bitSet = new BitSet(32);
            int anIndex;
            int counter;
            int min;
            int pathCount = paths.length;
            int validCount = 0;
            TreePath[] tempPath = new TreePath[1];
            tempPath[0] = paths[0];
            min = rowMapper.getRowsForPaths(tempPath)[0];
            for (counter = 0; counter < pathCount; counter++) {
                if (paths[counter] != null) {
                    tempPath[0] = paths[counter];
                    int[] rows = rowMapper.getRowsForPaths(tempPath);
                    if (rows == null) {
                        return false;
                    }
                    anIndex = rows[0];
                    if (anIndex == -1 || anIndex < (min - pathCount) || anIndex > (min + pathCount)) return false;
                    if (anIndex < min) min = anIndex;
                    if (!bitSet.get(anIndex)) {
                        bitSet.set(anIndex);
                        validCount++;
                    }
                }
            }
            int maxCounter = validCount + min;
            for (counter = min; counter < maxCounter; counter++) if (!bitSet.get(counter)) return false;
        }
        return true;
    }
    
    protected boolean canPathsBeAdded(TreePath[] paths) {
        if (paths == null || paths.length == 0 || rowMapper == null || selection == null || selectionMode == TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION) return true; else {
            BitSet bitSet = new BitSet();
            DefaultListSelectionModel lModel = listSelectionModel;
            int anIndex;
            int counter;
            int min = lModel.getMinSelectionIndex();
            int max = lModel.getMaxSelectionIndex();
            TreePath[] tempPath = new TreePath[1];
            if (min != -1) {
                for (counter = min; counter <= max; counter++) {
                    if (lModel.isSelectedIndex(counter)) bitSet.set(counter);
                }
            } else {
                tempPath[0] = paths[0];
                min = max = rowMapper.getRowsForPaths(tempPath)[0];
            }
            for (counter = paths.length - 1; counter >= 0; counter--) {
                if (paths[counter] != null) {
                    tempPath[0] = paths[counter];
                    int[] rows = rowMapper.getRowsForPaths(tempPath);
                    if (rows == null) {
                        return false;
                    }
                    anIndex = rows[0];
                    min = Math.min(anIndex, min);
                    max = Math.max(anIndex, max);
                    if (anIndex == -1) return false;
                    bitSet.set(anIndex);
                }
            }
            for (counter = min; counter <= max; counter++) if (!bitSet.get(counter)) return false;
        }
        return true;
    }
    
    protected boolean canPathsBeRemoved(TreePath[] paths) {
        if (rowMapper == null || selection == null || selectionMode == TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION) return true; else {
            BitSet bitSet = new BitSet();
            int counter;
            int pathCount = paths.length;
            int anIndex;
            int min = -1;
            int validCount = 0;
            TreePath[] tempPath = new TreePath[1];
            int[] rows;
            lastPaths.clear();
            for (counter = 0; counter < pathCount; counter++) {
                if (paths[counter] != null) {
                    lastPaths.put(paths[counter], Boolean.TRUE);
                }
            }
            for (counter = selection.length - 1; counter >= 0; counter--) {
                if (lastPaths.get(selection[counter]) == null) {
                    tempPath[0] = selection[counter];
                    rows = rowMapper.getRowsForPaths(tempPath);
                    if (rows != null && rows[0] != -1 && !bitSet.get(rows[0])) {
                        validCount++;
                        if (min == -1) min = rows[0]; else min = Math.min(min, rows[0]);
                        bitSet.set(rows[0]);
                    }
                }
            }
            lastPaths.clear();
            if (validCount > 1) {
                for (counter = min + validCount - 1; counter >= min; counter--) if (!bitSet.get(counter)) return false;
            }
        }
        return true;
    }
    
    protected void notifyPathChange(Vector changedPaths, TreePath oldLeadSelection) {
        int cPathCount = changedPaths.size();
        boolean[] newness = new boolean[cPathCount];
        TreePath[] paths = new TreePath[cPathCount];
        PathPlaceHolder placeholder;
        for (int counter = 0; counter < cPathCount; counter++) {
            placeholder = (PathPlaceHolder)(PathPlaceHolder)changedPaths.elementAt(counter);
            newness[counter] = placeholder.isNew;
            paths[counter] = placeholder.path;
        }
        TreeSelectionEvent event = new TreeSelectionEvent(this, paths, newness, oldLeadSelection, leadPath);
        fireValueChanged(event);
    }
    
    protected void updateLeadIndex() {
        if (leadPath != null) {
            if (selection == null) {
                leadPath = null;
                leadIndex = leadRow = -1;
            } else {
                leadRow = leadIndex = -1;
                for (int counter = selection.length - 1; counter >= 0; counter--) {
                    if (selection[counter] == leadPath) {
                        leadIndex = counter;
                        break;
                    }
                }
            }
        } else {
            leadIndex = -1;
        }
    }
    
    protected void insureUniqueness() {
    }
    
    public String toString() {
        int selCount = getSelectionCount();
        StringBuffer retBuffer = new StringBuffer();
        int[] rows;
        if (rowMapper != null) rows = rowMapper.getRowsForPaths(selection); else rows = null;
        retBuffer.append(getClass().getName() + " " + hashCode() + " [ ");
        for (int counter = 0; counter < selCount; counter++) {
            if (rows != null) retBuffer.append(selection[counter].toString() + "@" + Integer.toString(rows[counter]) + " "); else retBuffer.append(selection[counter].toString() + " ");
        }
        retBuffer.append("]");
        return retBuffer.toString();
    }
    
    public Object clone() throws CloneNotSupportedException {
        DefaultTreeSelectionModel clone = (DefaultTreeSelectionModel)(DefaultTreeSelectionModel)super.clone();
        clone.changeSupport = null;
        if (selection != null) {
            int selLength = selection.length;
            clone.selection = new TreePath[selLength];
            System.arraycopy(selection, 0, clone.selection, 0, selLength);
        }
        clone.listenerList = new EventListenerList();
        clone.listSelectionModel = (DefaultListSelectionModel)(DefaultListSelectionModel)listSelectionModel.clone();
        clone.uniquePaths = new Hashtable();
        clone.lastPaths = new Hashtable();
        clone.tempPaths = new TreePath[1];
        return clone;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        Object[] tValues;
        s.defaultWriteObject();
        if (rowMapper != null && rowMapper instanceof Serializable) {
            tValues = new Object[2];
            tValues[0] = "rowMapper";
            tValues[1] = rowMapper;
        } else tValues = new Object[0];
        s.writeObject(tValues);
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        Object[] tValues;
        s.defaultReadObject();
        tValues = (Object[])(Object[])s.readObject();
        if (tValues.length > 0 && tValues[0].equals("rowMapper")) rowMapper = (RowMapper)(RowMapper)tValues[1];
    }
}
