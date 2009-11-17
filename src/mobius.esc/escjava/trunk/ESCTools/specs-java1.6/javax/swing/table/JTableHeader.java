package javax.swing.table;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JTableHeader extends JComponent implements TableColumnModelListener, Accessible {
    
    /*synthetic*/ static TableCellRenderer access$100(JTableHeader x0) {
        return x0.defaultRenderer;
    }
    {
    }
    private static final String uiClassID = "TableHeaderUI";
    protected JTable table;
    protected TableColumnModel columnModel;
    protected boolean reorderingAllowed;
    protected boolean resizingAllowed;
    protected boolean updateTableInRealTime;
    protected transient TableColumn resizingColumn;
    protected transient TableColumn draggedColumn;
    protected transient int draggedDistance;
    private TableCellRenderer defaultRenderer;
    
    public JTableHeader() {
        this(null);
    }
    
    public JTableHeader(TableColumnModel cm) {
        
        setFocusable(false);
        if (cm == null) cm = createDefaultColumnModel();
        setColumnModel(cm);
        initializeLocalVars();
        updateUI();
    }
    
    public void setTable(JTable table) {
        JTable old = this.table;
        this.table = table;
        firePropertyChange("table", old, table);
    }
    
    public JTable getTable() {
        return table;
    }
    
    public void setReorderingAllowed(boolean reorderingAllowed) {
        boolean old = this.reorderingAllowed;
        this.reorderingAllowed = reorderingAllowed;
        firePropertyChange("reorderingAllowed", old, reorderingAllowed);
    }
    
    public boolean getReorderingAllowed() {
        return reorderingAllowed;
    }
    
    public void setResizingAllowed(boolean resizingAllowed) {
        boolean old = this.resizingAllowed;
        this.resizingAllowed = resizingAllowed;
        firePropertyChange("resizingAllowed", old, resizingAllowed);
    }
    
    public boolean getResizingAllowed() {
        return resizingAllowed;
    }
    
    public TableColumn getDraggedColumn() {
        return draggedColumn;
    }
    
    public int getDraggedDistance() {
        return draggedDistance;
    }
    
    public TableColumn getResizingColumn() {
        return resizingColumn;
    }
    
    public void setUpdateTableInRealTime(boolean flag) {
        updateTableInRealTime = flag;
    }
    
    public boolean getUpdateTableInRealTime() {
        return updateTableInRealTime;
    }
    
    public void setDefaultRenderer(TableCellRenderer defaultRenderer) {
        this.defaultRenderer = defaultRenderer;
    }
    
    public TableCellRenderer getDefaultRenderer() {
        return defaultRenderer;
    }
    
    public int columnAtPoint(Point point) {
        int x = point.x;
        if (!getComponentOrientation().isLeftToRight()) {
            x = getWidthInRightToLeft() - x;
        }
        return getColumnModel().getColumnIndexAtX(x);
    }
    
    public Rectangle getHeaderRect(int column) {
        Rectangle r = new Rectangle();
        TableColumnModel cm = getColumnModel();
        r.height = getHeight();
        if (column < 0) {
            if (!getComponentOrientation().isLeftToRight()) {
                r.x = getWidthInRightToLeft();
            }
        } else if (column >= cm.getColumnCount()) {
            if (getComponentOrientation().isLeftToRight()) {
                r.x = getWidth();
            }
        } else {
            for (int i = 0; i < column; i++) {
                r.x += cm.getColumn(i).getWidth();
            }
            if (!getComponentOrientation().isLeftToRight()) {
                r.x = getWidthInRightToLeft() - r.x - cm.getColumn(column).getWidth();
            }
            r.width = cm.getColumn(column).getWidth();
        }
        return r;
    }
    
    public String getToolTipText(MouseEvent event) {
        String tip = null;
        Point p = event.getPoint();
        int column;
        if ((column = columnAtPoint(p)) != -1) {
            TableColumn aColumn = columnModel.getColumn(column);
            TableCellRenderer renderer = aColumn.getHeaderRenderer();
            if (renderer == null) {
                renderer = defaultRenderer;
            }
            Component component = renderer.getTableCellRendererComponent(getTable(), aColumn.getHeaderValue(), false, false, -1, column);
            if (component instanceof JComponent) {
                MouseEvent newEvent;
                Rectangle cellRect = getHeaderRect(column);
                p.translate(-cellRect.x, -cellRect.y);
                newEvent = new MouseEvent(component, event.getID(), event.getWhen(), event.getModifiers(), p.x, p.y, event.getClickCount(), event.isPopupTrigger());
                tip = ((JComponent)(JComponent)component).getToolTipText(newEvent);
            }
        }
        if (tip == null) tip = getToolTipText();
        return tip;
    }
    
    public TableHeaderUI getUI() {
        return (TableHeaderUI)(TableHeaderUI)ui;
    }
    
    public void setUI(TableHeaderUI ui) {
        if (this.ui != ui) {
            super.setUI(ui);
            repaint();
        }
    }
    
    public void updateUI() {
        setUI((TableHeaderUI)(TableHeaderUI)UIManager.getUI(this));
        resizeAndRepaint();
        invalidate();
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public void setColumnModel(TableColumnModel columnModel) {
        if (columnModel == null) {
            throw new IllegalArgumentException("Cannot set a null ColumnModel");
        }
        TableColumnModel old = this.columnModel;
        if (columnModel != old) {
            if (old != null) {
                old.removeColumnModelListener(this);
            }
            this.columnModel = columnModel;
            columnModel.addColumnModelListener(this);
            firePropertyChange("columnModel", old, columnModel);
            resizeAndRepaint();
        }
    }
    
    public TableColumnModel getColumnModel() {
        return columnModel;
    }
    
    public void columnAdded(TableColumnModelEvent e) {
        resizeAndRepaint();
    }
    
    public void columnRemoved(TableColumnModelEvent e) {
        resizeAndRepaint();
    }
    
    public void columnMoved(TableColumnModelEvent e) {
        repaint();
    }
    
    public void columnMarginChanged(ChangeEvent e) {
        resizeAndRepaint();
    }
    
    public void columnSelectionChanged(ListSelectionEvent e) {
    }
    
    protected TableColumnModel createDefaultColumnModel() {
        return new DefaultTableColumnModel();
    }
    
    protected TableCellRenderer createDefaultRenderer() {
        DefaultTableCellRenderer label = new JTableHeader$UIResourceTableCellRenderer(null);
        label.setHorizontalAlignment(JLabel.CENTER);
        return label;
    }
    {
    }
    
    protected void initializeLocalVars() {
        setOpaque(true);
        table = null;
        reorderingAllowed = true;
        resizingAllowed = true;
        draggedColumn = null;
        draggedDistance = 0;
        resizingColumn = null;
        updateTableInRealTime = true;
        ToolTipManager toolTipManager = ToolTipManager.sharedInstance();
        toolTipManager.registerComponent(this);
        setDefaultRenderer(createDefaultRenderer());
    }
    
    public void resizeAndRepaint() {
        revalidate();
        repaint();
    }
    
    public void setDraggedColumn(TableColumn aColumn) {
        draggedColumn = aColumn;
    }
    
    public void setDraggedDistance(int distance) {
        draggedDistance = distance;
    }
    
    public void setResizingColumn(TableColumn aColumn) {
        resizingColumn = aColumn;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if ((ui != null) && (getUIClassID().equals(uiClassID))) {
            ui.installUI(this);
        }
    }
    
    private int getWidthInRightToLeft() {
        if ((table != null) && (table.getAutoResizeMode() != JTable.AUTO_RESIZE_OFF)) {
            return table.getWidth();
        }
        return super.getWidth();
    }
    
    protected String paramString() {
        String reorderingAllowedString = (reorderingAllowed ? "true" : "false");
        String resizingAllowedString = (resizingAllowed ? "true" : "false");
        String updateTableInRealTimeString = (updateTableInRealTime ? "true" : "false");
        return super.paramString() + ",draggedDistance=" + draggedDistance + ",reorderingAllowed=" + reorderingAllowedString + ",resizingAllowed=" + resizingAllowedString + ",updateTableInRealTime=" + updateTableInRealTimeString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JTableHeader$AccessibleJTableHeader(this);
        }
        return accessibleContext;
    }
    {
    }
}
