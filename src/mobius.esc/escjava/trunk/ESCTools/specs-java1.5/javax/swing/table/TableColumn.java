package javax.swing.table;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.SwingPropertyChangeSupport;
import java.lang.Integer;
import java.awt.Component;
import java.io.Serializable;
import java.beans.PropertyChangeListener;

public class TableColumn extends Object implements Serializable {
    public static final String COLUMN_WIDTH_PROPERTY = "columWidth";
    public static final String HEADER_VALUE_PROPERTY = "headerValue";
    public static final String HEADER_RENDERER_PROPERTY = "headerRenderer";
    public static final String CELL_RENDERER_PROPERTY = "cellRenderer";
    protected int modelIndex;
    protected Object identifier;
    protected int width;
    protected int minWidth;
    private int preferredWidth;
    protected int maxWidth;
    protected TableCellRenderer headerRenderer;
    protected Object headerValue;
    protected TableCellRenderer cellRenderer;
    protected TableCellEditor cellEditor;
    protected boolean isResizable;
    
    protected transient int resizedPostingDisableCount;
    private SwingPropertyChangeSupport changeSupport;
    
    public TableColumn() {
        this(0);
    }
    
    public TableColumn(int modelIndex) {
        this(modelIndex, 75, null, null);
    }
    
    public TableColumn(int modelIndex, int width) {
        this(modelIndex, width, null, null);
    }
    
    public TableColumn(int modelIndex, int width, TableCellRenderer cellRenderer, TableCellEditor cellEditor) {
        
        this.modelIndex = modelIndex;
        this.width = width;
        this.preferredWidth = width;
        this.cellRenderer = cellRenderer;
        this.cellEditor = cellEditor;
        minWidth = 15;
        maxWidth = Integer.MAX_VALUE;
        isResizable = true;
        resizedPostingDisableCount = 0;
        headerValue = null;
    }
    
    private void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
        if (changeSupport != null) {
            changeSupport.firePropertyChange(propertyName, oldValue, newValue);
        }
    }
    
    private void firePropertyChange(String propertyName, int oldValue, int newValue) {
        if (oldValue != newValue) {
            firePropertyChange(propertyName, new Integer(oldValue), new Integer(newValue));
        }
    }
    
    private void firePropertyChange(String propertyName, boolean oldValue, boolean newValue) {
        if (oldValue != newValue) {
            firePropertyChange(propertyName, Boolean.valueOf(oldValue), Boolean.valueOf(newValue));
        }
    }
    
    public void setModelIndex(int modelIndex) {
        int old = this.modelIndex;
        this.modelIndex = modelIndex;
        firePropertyChange("modelIndex", old, modelIndex);
    }
    
    public int getModelIndex() {
        return modelIndex;
    }
    
    public void setIdentifier(Object identifier) {
        Object old = this.identifier;
        this.identifier = identifier;
        firePropertyChange("identifier", old, identifier);
    }
    
    public Object getIdentifier() {
        return (identifier != null) ? identifier : getHeaderValue();
    }
    
    public void setHeaderValue(Object headerValue) {
        Object old = this.headerValue;
        this.headerValue = headerValue;
        firePropertyChange("headerValue", old, headerValue);
    }
    
    public Object getHeaderValue() {
        return headerValue;
    }
    
    public void setHeaderRenderer(TableCellRenderer headerRenderer) {
        TableCellRenderer old = this.headerRenderer;
        this.headerRenderer = headerRenderer;
        firePropertyChange("headerRenderer", old, headerRenderer);
    }
    
    public TableCellRenderer getHeaderRenderer() {
        return headerRenderer;
    }
    
    public void setCellRenderer(TableCellRenderer cellRenderer) {
        TableCellRenderer old = this.cellRenderer;
        this.cellRenderer = cellRenderer;
        firePropertyChange("cellRenderer", old, cellRenderer);
    }
    
    public TableCellRenderer getCellRenderer() {
        return cellRenderer;
    }
    
    public void setCellEditor(TableCellEditor cellEditor) {
        TableCellEditor old = this.cellEditor;
        this.cellEditor = cellEditor;
        firePropertyChange("cellEditor", old, cellEditor);
    }
    
    public TableCellEditor getCellEditor() {
        return cellEditor;
    }
    
    public void setWidth(int width) {
        int old = this.width;
        this.width = Math.min(Math.max(width, minWidth), maxWidth);
        firePropertyChange("width", old, this.width);
    }
    
    public int getWidth() {
        return width;
    }
    
    public void setPreferredWidth(int preferredWidth) {
        int old = this.preferredWidth;
        this.preferredWidth = Math.min(Math.max(preferredWidth, minWidth), maxWidth);
        firePropertyChange("preferredWidth", old, this.preferredWidth);
    }
    
    public int getPreferredWidth() {
        return preferredWidth;
    }
    
    public void setMinWidth(int minWidth) {
        int old = this.minWidth;
        this.minWidth = Math.max(minWidth, 0);
        if (width < minWidth) {
            setWidth(minWidth);
        }
        if (preferredWidth < minWidth) {
            setPreferredWidth(minWidth);
        }
        firePropertyChange("minWidth", old, this.minWidth);
    }
    
    public int getMinWidth() {
        return minWidth;
    }
    
    public void setMaxWidth(int maxWidth) {
        int old = this.maxWidth;
        this.maxWidth = Math.max(minWidth, maxWidth);
        if (width > maxWidth) {
            setWidth(maxWidth);
        }
        if (preferredWidth > maxWidth) {
            setPreferredWidth(maxWidth);
        }
        firePropertyChange("maxWidth", old, this.maxWidth);
    }
    
    public int getMaxWidth() {
        return maxWidth;
    }
    
    public void setResizable(boolean isResizable) {
        boolean old = this.isResizable;
        this.isResizable = isResizable;
        firePropertyChange("isResizable", old, this.isResizable);
    }
    
    public boolean getResizable() {
        return isResizable;
    }
    
    public void sizeWidthToFit() {
        if (headerRenderer == null) {
            return;
        }
        Component c = headerRenderer.getTableCellRendererComponent(null, getHeaderValue(), false, false, 0, 0);
        setMinWidth(c.getMinimumSize().width);
        setMaxWidth(c.getMaximumSize().width);
        setPreferredWidth(c.getPreferredSize().width);
        setWidth(getPreferredWidth());
    }
    
    
    public void disableResizedPosting() {
        resizedPostingDisableCount++;
    }
    
    
    public void enableResizedPosting() {
        resizedPostingDisableCount--;
    }
    
    public synchronized void addPropertyChangeListener(PropertyChangeListener listener) {
        if (changeSupport == null) {
            changeSupport = new SwingPropertyChangeSupport(this);
        }
        changeSupport.addPropertyChangeListener(listener);
    }
    
    public synchronized void removePropertyChangeListener(PropertyChangeListener listener) {
        if (changeSupport != null) {
            changeSupport.removePropertyChangeListener(listener);
        }
    }
    
    public synchronized PropertyChangeListener[] getPropertyChangeListeners() {
        if (changeSupport == null) {
            return new PropertyChangeListener[0];
        }
        return changeSupport.getPropertyChangeListeners();
    }
    
    protected TableCellRenderer createDefaultHeaderRenderer() {
        DefaultTableCellRenderer label = new TableColumn$1(this);
        label.setHorizontalAlignment(JLabel.CENTER);
        return label;
    }
}
