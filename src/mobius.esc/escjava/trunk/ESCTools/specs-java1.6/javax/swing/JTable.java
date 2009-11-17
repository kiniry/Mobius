package javax.swing;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.print.*;
import java.beans.*;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import javax.accessibility.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.table.*;
import javax.swing.border.*;
import java.text.MessageFormat;
import javax.print.attribute.*;

public class JTable extends JComponent implements TableModelListener, Scrollable, TableColumnModelListener, ListSelectionListener, CellEditorListener, Accessible {
    
    /*synthetic*/ static boolean access$102(JTable x0, boolean x1) {
        return x0.isPrinting = x1;
    }
    
    /*synthetic*/ static Throwable access$002(JTable x0, Throwable x1) {
        return x0.printError = x1;
    }
    private static final String uiClassID = "TableUI";
    public static final int AUTO_RESIZE_OFF = 0;
    public static final int AUTO_RESIZE_NEXT_COLUMN = 1;
    public static final int AUTO_RESIZE_SUBSEQUENT_COLUMNS = 2;
    public static final int AUTO_RESIZE_LAST_COLUMN = 3;
    public static final int AUTO_RESIZE_ALL_COLUMNS = 4;
    {
    }
    protected TableModel dataModel;
    protected TableColumnModel columnModel;
    protected ListSelectionModel selectionModel;
    protected JTableHeader tableHeader;
    protected int rowHeight;
    protected int rowMargin;
    protected Color gridColor;
    protected boolean showHorizontalLines;
    protected boolean showVerticalLines;
    protected int autoResizeMode;
    protected boolean autoCreateColumnsFromModel;
    protected Dimension preferredViewportSize;
    protected boolean rowSelectionAllowed;
    protected boolean cellSelectionEnabled;
    protected transient Component editorComp;
    protected transient TableCellEditor cellEditor;
    protected transient int editingColumn;
    protected transient int editingRow;
    protected transient Hashtable defaultRenderersByColumnClass;
    protected transient Hashtable defaultEditorsByColumnClass;
    protected Color selectionForeground;
    protected Color selectionBackground;
    private SizeSequence rowModel;
    private boolean dragEnabled;
    private boolean surrendersFocusOnKeystroke;
    private PropertyChangeListener editorRemover = null;
    private boolean columnSelectionAdjusting;
    private boolean rowSelectionAdjusting;
    private boolean isPrinting = false;
    private Throwable printError;
    private boolean isRowHeightSet;
    
    public JTable() {
        this(null, null, null);
    }
    
    public JTable(TableModel dm) {
        this(dm, null, null);
    }
    
    public JTable(TableModel dm, TableColumnModel cm) {
        this(dm, cm, null);
    }
    
    public JTable(TableModel dm, TableColumnModel cm, ListSelectionModel sm) {
        
        setLayout(null);
        setFocusTraversalKeys(KeyboardFocusManager.FORWARD_TRAVERSAL_KEYS, JComponent.getManagingFocusForwardTraversalKeys());
        setFocusTraversalKeys(KeyboardFocusManager.BACKWARD_TRAVERSAL_KEYS, JComponent.getManagingFocusBackwardTraversalKeys());
        if (cm == null) {
            cm = createDefaultColumnModel();
            autoCreateColumnsFromModel = true;
        }
        setColumnModel(cm);
        if (sm == null) {
            sm = createDefaultSelectionModel();
        }
        setSelectionModel(sm);
        if (dm == null) {
            dm = createDefaultDataModel();
        }
        setModel(dm);
        initializeLocalVars();
        updateUI();
    }
    
    public JTable(int numRows, int numColumns) {
        this(new DefaultTableModel(numRows, numColumns));
    }
    
    public JTable(Vector rowData, Vector columnNames) {
        this(new DefaultTableModel(rowData, columnNames));
    }
    
    public JTable(final Object[][] rowData, final Object[] columnNames) {
        this(new JTable$1(columnNames, rowData));
    }
    
    public void addNotify() {
        super.addNotify();
        configureEnclosingScrollPane();
    }
    
    protected void configureEnclosingScrollPane() {
        Container p = getParent();
        if (p instanceof JViewport) {
            Container gp = p.getParent();
            if (gp instanceof JScrollPane) {
                JScrollPane scrollPane = (JScrollPane)(JScrollPane)gp;
                JViewport viewport = scrollPane.getViewport();
                if (viewport == null || viewport.getView() != this) {
                    return;
                }
                scrollPane.setColumnHeaderView(getTableHeader());
                Border border = scrollPane.getBorder();
                if (border == null || border instanceof UIResource) {
                    scrollPane.setBorder(UIManager.getBorder("Table.scrollPaneBorder"));
                }
            }
        }
    }
    
    public void removeNotify() {
        KeyboardFocusManager.getCurrentKeyboardFocusManager().removePropertyChangeListener("permanentFocusOwner", editorRemover);
        editorRemover = null;
        unconfigureEnclosingScrollPane();
        super.removeNotify();
    }
    
    protected void unconfigureEnclosingScrollPane() {
        Container p = getParent();
        if (p instanceof JViewport) {
            Container gp = p.getParent();
            if (gp instanceof JScrollPane) {
                JScrollPane scrollPane = (JScrollPane)(JScrollPane)gp;
                JViewport viewport = scrollPane.getViewport();
                if (viewport == null || viewport.getView() != this) {
                    return;
                }
                scrollPane.setColumnHeaderView(null);
            }
        }
    }
    
    void setUIProperty(String propertyName, Object value) {
        if (propertyName == "rowHeight") {
            if (!isRowHeightSet) {
                setRowHeight(((Number)(Number)value).intValue());
                isRowHeightSet = false;
            }
            return;
        }
        super.setUIProperty(propertyName, value);
    }
    
    
    public static JScrollPane createScrollPaneForTable(JTable aTable) {
        return new JScrollPane(aTable);
    }
    
    public void setTableHeader(JTableHeader tableHeader) {
        if (this.tableHeader != tableHeader) {
            JTableHeader old = this.tableHeader;
            if (old != null) {
                old.setTable(null);
            }
            this.tableHeader = tableHeader;
            if (tableHeader != null) {
                tableHeader.setTable(this);
            }
            firePropertyChange("tableHeader", old, tableHeader);
        }
    }
    
    public JTableHeader getTableHeader() {
        return tableHeader;
    }
    
    public void setRowHeight(int rowHeight) {
        if (rowHeight <= 0) {
            throw new IllegalArgumentException("New row height less than 1");
        }
        int old = this.rowHeight;
        this.rowHeight = rowHeight;
        rowModel = null;
        isRowHeightSet = true;
        resizeAndRepaint();
        firePropertyChange("rowHeight", old, rowHeight);
    }
    
    public int getRowHeight() {
        return rowHeight;
    }
    
    private SizeSequence getRowModel() {
        if (rowModel == null) {
            rowModel = new SizeSequence(getRowCount(), getRowHeight());
        }
        return rowModel;
    }
    
    public void setRowHeight(int row, int rowHeight) {
        if (rowHeight <= 0) {
            throw new IllegalArgumentException("New row height less than 1");
        }
        getRowModel().setSize(row, rowHeight);
        resizeAndRepaint();
    }
    
    public int getRowHeight(int row) {
        return (rowModel == null) ? getRowHeight() : rowModel.getSize(row);
    }
    
    public void setRowMargin(int rowMargin) {
        int old = this.rowMargin;
        this.rowMargin = rowMargin;
        resizeAndRepaint();
        firePropertyChange("rowMargin", old, rowMargin);
    }
    
    public int getRowMargin() {
        return rowMargin;
    }
    
    public void setIntercellSpacing(Dimension intercellSpacing) {
        setRowMargin(intercellSpacing.height);
        getColumnModel().setColumnMargin(intercellSpacing.width);
        resizeAndRepaint();
    }
    
    public Dimension getIntercellSpacing() {
        return new Dimension(getColumnModel().getColumnMargin(), rowMargin);
    }
    
    public void setGridColor(Color gridColor) {
        if (gridColor == null) {
            throw new IllegalArgumentException("New color is null");
        }
        Color old = this.gridColor;
        this.gridColor = gridColor;
        firePropertyChange("gridColor", old, gridColor);
        repaint();
    }
    
    public Color getGridColor() {
        return gridColor;
    }
    
    public void setShowGrid(boolean showGrid) {
        setShowHorizontalLines(showGrid);
        setShowVerticalLines(showGrid);
        repaint();
    }
    
    public void setShowHorizontalLines(boolean showHorizontalLines) {
        boolean old = this.showHorizontalLines;
        this.showHorizontalLines = showHorizontalLines;
        firePropertyChange("showHorizontalLines", old, showHorizontalLines);
        repaint();
    }
    
    public void setShowVerticalLines(boolean showVerticalLines) {
        boolean old = this.showVerticalLines;
        this.showVerticalLines = showVerticalLines;
        firePropertyChange("showVerticalLines", old, showVerticalLines);
        repaint();
    }
    
    public boolean getShowHorizontalLines() {
        return showHorizontalLines;
    }
    
    public boolean getShowVerticalLines() {
        return showVerticalLines;
    }
    
    public void setAutoResizeMode(int mode) {
        if ((mode == AUTO_RESIZE_OFF) || (mode == AUTO_RESIZE_NEXT_COLUMN) || (mode == AUTO_RESIZE_SUBSEQUENT_COLUMNS) || (mode == AUTO_RESIZE_LAST_COLUMN) || (mode == AUTO_RESIZE_ALL_COLUMNS)) {
            int old = autoResizeMode;
            autoResizeMode = mode;
            resizeAndRepaint();
            if (tableHeader != null) {
                tableHeader.resizeAndRepaint();
            }
            firePropertyChange("autoResizeMode", old, autoResizeMode);
        }
    }
    
    public int getAutoResizeMode() {
        return autoResizeMode;
    }
    
    public void setAutoCreateColumnsFromModel(boolean autoCreateColumnsFromModel) {
        if (this.autoCreateColumnsFromModel != autoCreateColumnsFromModel) {
            boolean old = this.autoCreateColumnsFromModel;
            this.autoCreateColumnsFromModel = autoCreateColumnsFromModel;
            if (autoCreateColumnsFromModel) {
                createDefaultColumnsFromModel();
            }
            firePropertyChange("autoCreateColumnsFromModel", old, autoCreateColumnsFromModel);
        }
    }
    
    public boolean getAutoCreateColumnsFromModel() {
        return autoCreateColumnsFromModel;
    }
    
    public void createDefaultColumnsFromModel() {
        TableModel m = getModel();
        if (m != null) {
            TableColumnModel cm = getColumnModel();
            while (cm.getColumnCount() > 0) {
                cm.removeColumn(cm.getColumn(0));
            }
            for (int i = 0; i < m.getColumnCount(); i++) {
                TableColumn newColumn = new TableColumn(i);
                addColumn(newColumn);
            }
        }
    }
    
    public void setDefaultRenderer(Class columnClass, TableCellRenderer renderer) {
        if (renderer != null) {
            defaultRenderersByColumnClass.put(columnClass, renderer);
        } else {
            defaultRenderersByColumnClass.remove(columnClass);
        }
    }
    
    public TableCellRenderer getDefaultRenderer(Class columnClass) {
        if (columnClass == null) {
            return null;
        } else {
            Object renderer = defaultRenderersByColumnClass.get(columnClass);
            if (renderer != null) {
                return (TableCellRenderer)(TableCellRenderer)renderer;
            } else {
                return getDefaultRenderer(columnClass.getSuperclass());
            }
        }
    }
    
    public void setDefaultEditor(Class columnClass, TableCellEditor editor) {
        if (editor != null) {
            defaultEditorsByColumnClass.put(columnClass, editor);
        } else {
            defaultEditorsByColumnClass.remove(columnClass);
        }
    }
    
    public TableCellEditor getDefaultEditor(Class columnClass) {
        if (columnClass == null) {
            return null;
        } else {
            Object editor = defaultEditorsByColumnClass.get(columnClass);
            if (editor != null) {
                return (TableCellEditor)(TableCellEditor)editor;
            } else {
                return getDefaultEditor(columnClass.getSuperclass());
            }
        }
    }
    
    public void setDragEnabled(boolean b) {
        if (b && GraphicsEnvironment.isHeadless()) {
            throw new HeadlessException();
        }
        dragEnabled = b;
    }
    
    public boolean getDragEnabled() {
        return dragEnabled;
    }
    
    public void setSelectionMode(int selectionMode) {
        clearSelection();
        getSelectionModel().setSelectionMode(selectionMode);
        getColumnModel().getSelectionModel().setSelectionMode(selectionMode);
    }
    
    public void setRowSelectionAllowed(boolean rowSelectionAllowed) {
        boolean old = this.rowSelectionAllowed;
        this.rowSelectionAllowed = rowSelectionAllowed;
        if (old != rowSelectionAllowed) {
            repaint();
        }
        firePropertyChange("rowSelectionAllowed", old, rowSelectionAllowed);
    }
    
    public boolean getRowSelectionAllowed() {
        return rowSelectionAllowed;
    }
    
    public void setColumnSelectionAllowed(boolean columnSelectionAllowed) {
        boolean old = columnModel.getColumnSelectionAllowed();
        columnModel.setColumnSelectionAllowed(columnSelectionAllowed);
        if (old != columnSelectionAllowed) {
            repaint();
        }
        firePropertyChange("columnSelectionAllowed", old, columnSelectionAllowed);
    }
    
    public boolean getColumnSelectionAllowed() {
        return columnModel.getColumnSelectionAllowed();
    }
    
    public void setCellSelectionEnabled(boolean cellSelectionEnabled) {
        setRowSelectionAllowed(cellSelectionEnabled);
        setColumnSelectionAllowed(cellSelectionEnabled);
        boolean old = this.cellSelectionEnabled;
        this.cellSelectionEnabled = cellSelectionEnabled;
        firePropertyChange("cellSelectionEnabled", old, cellSelectionEnabled);
    }
    
    public boolean getCellSelectionEnabled() {
        return getRowSelectionAllowed() && getColumnSelectionAllowed();
    }
    
    public void selectAll() {
        if (isEditing()) {
            removeEditor();
        }
        if (getRowCount() > 0 && getColumnCount() > 0) {
            int oldLead;
            int oldAnchor;
            ListSelectionModel selModel;
            selModel = selectionModel;
            selModel.setValueIsAdjusting(true);
            oldLead = getAdjustedIndex(selModel.getLeadSelectionIndex(), true);
            oldAnchor = getAdjustedIndex(selModel.getAnchorSelectionIndex(), true);
            setRowSelectionInterval(0, getRowCount() - 1);
            if (oldAnchor == -1) {
                oldAnchor = oldLead;
            }
            if (oldLead == -1) {
                selModel.setAnchorSelectionIndex(-1);
                selModel.setLeadSelectionIndex(-1);
            } else {
                selModel.addSelectionInterval(oldAnchor, oldLead);
            }
            selModel.setValueIsAdjusting(false);
            selModel = columnModel.getSelectionModel();
            selModel.setValueIsAdjusting(true);
            oldLead = getAdjustedIndex(selModel.getLeadSelectionIndex(), false);
            oldAnchor = getAdjustedIndex(selModel.getAnchorSelectionIndex(), false);
            setColumnSelectionInterval(0, getColumnCount() - 1);
            if (oldAnchor == -1) {
                oldAnchor = oldLead;
            }
            if (oldLead == -1) {
                selModel.setAnchorSelectionIndex(-1);
                selModel.setLeadSelectionIndex(-1);
            } else {
                selModel.addSelectionInterval(oldAnchor, oldLead);
            }
            selModel.setValueIsAdjusting(false);
        }
    }
    
    public void clearSelection() {
        selectionModel.clearSelection();
        columnModel.getSelectionModel().clearSelection();
    }
    
    private void clearSelectionAndLeadAnchor() {
        selectionModel.setValueIsAdjusting(true);
        columnModel.getSelectionModel().setValueIsAdjusting(true);
        clearSelection();
        selectionModel.setAnchorSelectionIndex(-1);
        selectionModel.setLeadSelectionIndex(-1);
        columnModel.getSelectionModel().setAnchorSelectionIndex(-1);
        columnModel.getSelectionModel().setLeadSelectionIndex(-1);
        selectionModel.setValueIsAdjusting(false);
        columnModel.getSelectionModel().setValueIsAdjusting(false);
    }
    
    private int getAdjustedIndex(int index, boolean row) {
        int compare = row ? getRowCount() : getColumnCount();
        return index < compare ? index : -1;
    }
    
    private int boundRow(int row) throws IllegalArgumentException {
        if (row < 0 || row >= getRowCount()) {
            throw new IllegalArgumentException("Row index out of range");
        }
        return row;
    }
    
    private int boundColumn(int col) {
        if (col < 0 || col >= getColumnCount()) {
            throw new IllegalArgumentException("Column index out of range");
        }
        return col;
    }
    
    public void setRowSelectionInterval(int index0, int index1) {
        selectionModel.setSelectionInterval(boundRow(index0), boundRow(index1));
    }
    
    public void setColumnSelectionInterval(int index0, int index1) {
        columnModel.getSelectionModel().setSelectionInterval(boundColumn(index0), boundColumn(index1));
    }
    
    public void addRowSelectionInterval(int index0, int index1) {
        selectionModel.addSelectionInterval(boundRow(index0), boundRow(index1));
    }
    
    public void addColumnSelectionInterval(int index0, int index1) {
        columnModel.getSelectionModel().addSelectionInterval(boundColumn(index0), boundColumn(index1));
    }
    
    public void removeRowSelectionInterval(int index0, int index1) {
        selectionModel.removeSelectionInterval(boundRow(index0), boundRow(index1));
    }
    
    public void removeColumnSelectionInterval(int index0, int index1) {
        columnModel.getSelectionModel().removeSelectionInterval(boundColumn(index0), boundColumn(index1));
    }
    
    public int getSelectedRow() {
        return selectionModel.getMinSelectionIndex();
    }
    
    public int getSelectedColumn() {
        return columnModel.getSelectionModel().getMinSelectionIndex();
    }
    
    public int[] getSelectedRows() {
        int iMin = selectionModel.getMinSelectionIndex();
        int iMax = selectionModel.getMaxSelectionIndex();
        if ((iMin == -1) || (iMax == -1)) {
            return new int[0];
        }
        int[] rvTmp = new int[1 + (iMax - iMin)];
        int n = 0;
        for (int i = iMin; i <= iMax; i++) {
            if (selectionModel.isSelectedIndex(i)) {
                rvTmp[n++] = i;
            }
        }
        int[] rv = new int[n];
        System.arraycopy(rvTmp, 0, rv, 0, n);
        return rv;
    }
    
    public int[] getSelectedColumns() {
        return columnModel.getSelectedColumns();
    }
    
    public int getSelectedRowCount() {
        int iMin = selectionModel.getMinSelectionIndex();
        int iMax = selectionModel.getMaxSelectionIndex();
        int count = 0;
        for (int i = iMin; i <= iMax; i++) {
            if (selectionModel.isSelectedIndex(i)) {
                count++;
            }
        }
        return count;
    }
    
    public int getSelectedColumnCount() {
        return columnModel.getSelectedColumnCount();
    }
    
    public boolean isRowSelected(int row) {
        return selectionModel.isSelectedIndex(row);
    }
    
    public boolean isColumnSelected(int column) {
        return columnModel.getSelectionModel().isSelectedIndex(column);
    }
    
    public boolean isCellSelected(int row, int column) {
        if (!getRowSelectionAllowed() && !getColumnSelectionAllowed()) {
            return false;
        }
        return (!getRowSelectionAllowed() || isRowSelected(row)) && (!getColumnSelectionAllowed() || isColumnSelected(column));
    }
    
    private void changeSelectionModel(ListSelectionModel sm, int index, boolean toggle, boolean extend, boolean selected, boolean row) {
        if (extend) {
            if (toggle) {
                sm.setAnchorSelectionIndex(index);
            } else {
                int anchorIndex = getAdjustedIndex(sm.getAnchorSelectionIndex(), row);
                if (anchorIndex == -1) {
                    anchorIndex = 0;
                }
                sm.setSelectionInterval(anchorIndex, index);
            }
        } else {
            if (toggle) {
                if (selected) {
                    sm.removeSelectionInterval(index, index);
                } else {
                    sm.addSelectionInterval(index, index);
                }
            } else {
                sm.setSelectionInterval(index, index);
            }
        }
    }
    
    public void changeSelection(int rowIndex, int columnIndex, boolean toggle, boolean extend) {
        ListSelectionModel rsm = getSelectionModel();
        ListSelectionModel csm = getColumnModel().getSelectionModel();
        boolean selected = isCellSelected(rowIndex, columnIndex);
        changeSelectionModel(csm, columnIndex, toggle, extend, selected, false);
        changeSelectionModel(rsm, rowIndex, toggle, extend, selected, true);
        if (getAutoscrolls()) {
            Rectangle cellRect = getCellRect(rowIndex, columnIndex, false);
            if (cellRect != null) {
                scrollRectToVisible(cellRect);
            }
        }
    }
    
    public Color getSelectionForeground() {
        return selectionForeground;
    }
    
    public void setSelectionForeground(Color selectionForeground) {
        Color old = this.selectionForeground;
        this.selectionForeground = selectionForeground;
        firePropertyChange("selectionForeground", old, selectionForeground);
        if (!selectionForeground.equals(old)) {
            repaint();
        }
    }
    
    public Color getSelectionBackground() {
        return selectionBackground;
    }
    
    public void setSelectionBackground(Color selectionBackground) {
        Color old = this.selectionBackground;
        this.selectionBackground = selectionBackground;
        firePropertyChange("selectionBackground", old, selectionBackground);
        if (!selectionBackground.equals(old)) {
            repaint();
        }
    }
    
    public TableColumn getColumn(Object identifier) {
        TableColumnModel cm = getColumnModel();
        int columnIndex = cm.getColumnIndex(identifier);
        return cm.getColumn(columnIndex);
    }
    
    public int convertColumnIndexToModel(int viewColumnIndex) {
        if (viewColumnIndex < 0) {
            return viewColumnIndex;
        }
        return getColumnModel().getColumn(viewColumnIndex).getModelIndex();
    }
    
    public int convertColumnIndexToView(int modelColumnIndex) {
        if (modelColumnIndex < 0) {
            return modelColumnIndex;
        }
        TableColumnModel cm = getColumnModel();
        for (int column = 0; column < getColumnCount(); column++) {
            if (cm.getColumn(column).getModelIndex() == modelColumnIndex) {
                return column;
            }
        }
        return -1;
    }
    
    public int getRowCount() {
        return getModel().getRowCount();
    }
    
    public int getColumnCount() {
        return getColumnModel().getColumnCount();
    }
    
    public String getColumnName(int column) {
        return getModel().getColumnName(convertColumnIndexToModel(column));
    }
    
    public Class getColumnClass(int column) {
        return getModel().getColumnClass(convertColumnIndexToModel(column));
    }
    
    public Object getValueAt(int row, int column) {
        return getModel().getValueAt(row, convertColumnIndexToModel(column));
    }
    
    public void setValueAt(Object aValue, int row, int column) {
        getModel().setValueAt(aValue, row, convertColumnIndexToModel(column));
    }
    
    public boolean isCellEditable(int row, int column) {
        return getModel().isCellEditable(row, convertColumnIndexToModel(column));
    }
    
    public void addColumn(TableColumn aColumn) {
        if (aColumn.getHeaderValue() == null) {
            int modelColumn = aColumn.getModelIndex();
            String columnName = getModel().getColumnName(modelColumn);
            aColumn.setHeaderValue(columnName);
        }
        getColumnModel().addColumn(aColumn);
    }
    
    public void removeColumn(TableColumn aColumn) {
        getColumnModel().removeColumn(aColumn);
    }
    
    public void moveColumn(int column, int targetColumn) {
        getColumnModel().moveColumn(column, targetColumn);
    }
    
    public int columnAtPoint(Point point) {
        int x = point.x;
        if (!getComponentOrientation().isLeftToRight()) {
            x = getWidth() - x;
        }
        return getColumnModel().getColumnIndexAtX(x);
    }
    
    public int rowAtPoint(Point point) {
        int y = point.y;
        int result = (rowModel == null) ? y / getRowHeight() : rowModel.getIndex(y);
        if (result < 0) {
            return -1;
        } else if (result >= getRowCount()) {
            return -1;
        } else {
            return result;
        }
    }
    
    public Rectangle getCellRect(int row, int column, boolean includeSpacing) {
        Rectangle r = new Rectangle();
        boolean valid = true;
        if (row < 0) {
            valid = false;
        } else if (row >= getRowCount()) {
            r.y = getHeight();
            valid = false;
        } else {
            r.height = getRowHeight(row);
            r.y = (rowModel == null) ? row * r.height : rowModel.getPosition(row);
        }
        if (column < 0) {
            if (!getComponentOrientation().isLeftToRight()) {
                r.x = getWidth();
            }
            valid = false;
        } else if (column >= getColumnCount()) {
            if (getComponentOrientation().isLeftToRight()) {
                r.x = getWidth();
            }
            valid = false;
        } else {
            TableColumnModel cm = getColumnModel();
            if (getComponentOrientation().isLeftToRight()) {
                for (int i = 0; i < column; i++) {
                    r.x += cm.getColumn(i).getWidth();
                }
            } else {
                for (int i = cm.getColumnCount() - 1; i > column; i--) {
                    r.x += cm.getColumn(i).getWidth();
                }
            }
            r.width = cm.getColumn(column).getWidth();
        }
        if (valid && !includeSpacing) {
            int rm = getRowMargin();
            int cm = getColumnModel().getColumnMargin();
            r.setBounds(r.x + cm / 2, r.y + rm / 2, r.width - cm, r.height - rm);
        }
        return r;
    }
    
    private int viewIndexForColumn(TableColumn aColumn) {
        TableColumnModel cm = getColumnModel();
        for (int column = 0; column < cm.getColumnCount(); column++) {
            if (cm.getColumn(column) == aColumn) {
                return column;
            }
        }
        return -1;
    }
    
    public void doLayout() {
        TableColumn resizingColumn = getResizingColumn();
        if (resizingColumn == null) {
            setWidthsFromPreferredWidths(false);
        } else {
            int columnIndex = viewIndexForColumn(resizingColumn);
            int delta = getWidth() - getColumnModel().getTotalColumnWidth();
            accommodateDelta(columnIndex, delta);
            delta = getWidth() - getColumnModel().getTotalColumnWidth();
            if (delta != 0) {
                resizingColumn.setWidth(resizingColumn.getWidth() + delta);
            }
            setWidthsFromPreferredWidths(true);
        }
        super.doLayout();
    }
    
    private TableColumn getResizingColumn() {
        return (tableHeader == null) ? null : tableHeader.getResizingColumn();
    }
    
    
    public void sizeColumnsToFit(boolean lastColumnOnly) {
        int oldAutoResizeMode = autoResizeMode;
        setAutoResizeMode(lastColumnOnly ? AUTO_RESIZE_LAST_COLUMN : AUTO_RESIZE_ALL_COLUMNS);
        sizeColumnsToFit(-1);
        setAutoResizeMode(oldAutoResizeMode);
    }
    
    public void sizeColumnsToFit(int resizingColumn) {
        if (resizingColumn == -1) {
            setWidthsFromPreferredWidths(false);
        } else {
            if (autoResizeMode == AUTO_RESIZE_OFF) {
                TableColumn aColumn = getColumnModel().getColumn(resizingColumn);
                aColumn.setPreferredWidth(aColumn.getWidth());
            } else {
                int delta = getWidth() - getColumnModel().getTotalColumnWidth();
                accommodateDelta(resizingColumn, delta);
                setWidthsFromPreferredWidths(true);
            }
        }
    }
    
    private void setWidthsFromPreferredWidths(final boolean inverse) {
        int totalWidth = getWidth();
        int totalPreferred = getPreferredSize().width;
        int target = !inverse ? totalWidth : totalPreferred;
        final TableColumnModel cm = columnModel;
        JTable$Resizable3 r = new JTable$2(this, cm, inverse);
        adjustSizes(target, r, inverse);
    }
    
    private void accommodateDelta(int resizingColumnIndex, int delta) {
        int columnCount = getColumnCount();
        int from = resizingColumnIndex;
        int to = columnCount;
        switch (autoResizeMode) {
        case AUTO_RESIZE_NEXT_COLUMN: 
            from = from + 1;
            to = Math.min(from + 1, columnCount);
            break;
        
        case AUTO_RESIZE_SUBSEQUENT_COLUMNS: 
            from = from + 1;
            to = columnCount;
            break;
        
        case AUTO_RESIZE_LAST_COLUMN: 
            from = columnCount - 1;
            to = from + 1;
            break;
        
        case AUTO_RESIZE_ALL_COLUMNS: 
            from = 0;
            to = columnCount;
            break;
        
        default: 
            return;
        
        }
        final int start = from;
        final int end = to;
        final TableColumnModel cm = columnModel;
        JTable$Resizable3 r = new JTable$3(this, end, start, cm);
        int totalWidth = 0;
        for (int i = from; i < to; i++) {
            TableColumn aColumn = columnModel.getColumn(i);
            int input = aColumn.getWidth();
            totalWidth = totalWidth + input;
        }
        adjustSizes(totalWidth + delta, r, false);
        return;
    }
    {
    }
    {
    }
    
    private void adjustSizes(long target, final JTable$Resizable3 r, boolean inverse) {
        int N = r.getElementCount();
        long totalPreferred = 0;
        for (int i = 0; i < N; i++) {
            totalPreferred += r.getMidPointAt(i);
        }
        JTable$Resizable2 s;
        if ((target < totalPreferred) == !inverse) {
            s = new JTable$4(this, r);
        } else {
            s = new JTable$5(this, r);
        }
        adjustSizes(target, s, !inverse);
    }
    
    private void adjustSizes(long target, JTable$Resizable2 r, boolean limitToRange) {
        long totalLowerBound = 0;
        long totalUpperBound = 0;
        for (int i = 0; i < r.getElementCount(); i++) {
            totalLowerBound += r.getLowerBoundAt(i);
            totalUpperBound += r.getUpperBoundAt(i);
        }
        if (limitToRange) {
            target = Math.min(Math.max(totalLowerBound, target), totalUpperBound);
        }
        for (int i = 0; i < r.getElementCount(); i++) {
            int lowerBound = r.getLowerBoundAt(i);
            int upperBound = r.getUpperBoundAt(i);
            int newSize;
            if (totalLowerBound == totalUpperBound) {
                newSize = lowerBound;
            } else {
                double f = (double)(target - totalLowerBound) / (totalUpperBound - totalLowerBound);
                newSize = (int)Math.round(lowerBound + f * (upperBound - lowerBound));
            }
            r.setSizeAt(newSize, i);
            target -= newSize;
            totalLowerBound -= lowerBound;
            totalUpperBound -= upperBound;
        }
    }
    
    public String getToolTipText(MouseEvent event) {
        String tip = null;
        Point p = event.getPoint();
        int hitColumnIndex = columnAtPoint(p);
        int hitRowIndex = rowAtPoint(p);
        if ((hitColumnIndex != -1) && (hitRowIndex != -1)) {
            TableCellRenderer renderer = getCellRenderer(hitRowIndex, hitColumnIndex);
            Component component = prepareRenderer(renderer, hitRowIndex, hitColumnIndex);
            if (component instanceof JComponent) {
                Rectangle cellRect = getCellRect(hitRowIndex, hitColumnIndex, false);
                p.translate(-cellRect.x, -cellRect.y);
                MouseEvent newEvent = new MouseEvent(component, event.getID(), event.getWhen(), event.getModifiers(), p.x, p.y, event.getClickCount(), event.isPopupTrigger());
                tip = ((JComponent)(JComponent)component).getToolTipText(newEvent);
            }
        }
        if (tip == null) tip = getToolTipText();
        return tip;
    }
    
    public void setSurrendersFocusOnKeystroke(boolean surrendersFocusOnKeystroke) {
        this.surrendersFocusOnKeystroke = surrendersFocusOnKeystroke;
    }
    
    public boolean getSurrendersFocusOnKeystroke() {
        return surrendersFocusOnKeystroke;
    }
    
    public boolean editCellAt(int row, int column) {
        return editCellAt(row, column, null);
    }
    
    public boolean editCellAt(int row, int column, EventObject e) {
        if (cellEditor != null && !cellEditor.stopCellEditing()) {
            return false;
        }
        if (row < 0 || row >= getRowCount() || column < 0 || column >= getColumnCount()) {
            return false;
        }
        if (!isCellEditable(row, column)) return false;
        if (editorRemover == null) {
            KeyboardFocusManager fm = KeyboardFocusManager.getCurrentKeyboardFocusManager();
            editorRemover = new JTable$CellEditorRemover(this, fm);
            fm.addPropertyChangeListener("permanentFocusOwner", editorRemover);
        }
        TableCellEditor editor = getCellEditor(row, column);
        if (editor != null && editor.isCellEditable(e)) {
            editorComp = prepareEditor(editor, row, column);
            if (editorComp == null) {
                removeEditor();
                return false;
            }
            editorComp.setBounds(getCellRect(row, column, false));
            add(editorComp);
            editorComp.validate();
            setCellEditor(editor);
            setEditingRow(row);
            setEditingColumn(column);
            editor.addCellEditorListener(this);
            return true;
        }
        return false;
    }
    
    public boolean isEditing() {
        return (cellEditor == null) ? false : true;
    }
    
    public Component getEditorComponent() {
        return editorComp;
    }
    
    public int getEditingColumn() {
        return editingColumn;
    }
    
    public int getEditingRow() {
        return editingRow;
    }
    
    public TableUI getUI() {
        return (TableUI)(TableUI)ui;
    }
    
    public void setUI(TableUI ui) {
        if (this.ui != ui) {
            super.setUI(ui);
            repaint();
        }
    }
    
    private void updateSubComponentUI(Object componentShell) {
        if (componentShell == null) {
            return;
        }
        Component component = null;
        if (componentShell instanceof Component) {
            component = (Component)(Component)componentShell;
        }
        if (componentShell instanceof DefaultCellEditor) {
            component = ((DefaultCellEditor)(DefaultCellEditor)componentShell).getComponent();
        }
        if (component != null && component instanceof JComponent) {
            ((JComponent)(JComponent)component).updateUI();
        }
    }
    
    public void updateUI() {
        TableColumnModel cm = getColumnModel();
        for (int column = 0; column < cm.getColumnCount(); column++) {
            TableColumn aColumn = cm.getColumn(column);
            updateSubComponentUI(aColumn.getCellRenderer());
            updateSubComponentUI(aColumn.getCellEditor());
            updateSubComponentUI(aColumn.getHeaderRenderer());
        }
        Enumeration defaultRenderers = defaultRenderersByColumnClass.elements();
        while (defaultRenderers.hasMoreElements()) {
            updateSubComponentUI(defaultRenderers.nextElement());
        }
        Enumeration defaultEditors = defaultEditorsByColumnClass.elements();
        while (defaultEditors.hasMoreElements()) {
            updateSubComponentUI(defaultEditors.nextElement());
        }
        if (tableHeader != null && tableHeader.getParent() == null) {
            tableHeader.updateUI();
        }
        setUI((TableUI)(TableUI)UIManager.getUI(this));
        resizeAndRepaint();
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public void setModel(TableModel dataModel) {
        if (dataModel == null) {
            throw new IllegalArgumentException("Cannot set a null TableModel");
        }
        if (this.dataModel != dataModel) {
            TableModel old = this.dataModel;
            if (old != null) {
                old.removeTableModelListener(this);
            }
            this.dataModel = dataModel;
            dataModel.addTableModelListener(this);
            tableChanged(new TableModelEvent(dataModel, TableModelEvent.HEADER_ROW));
            firePropertyChange("model", old, dataModel);
        }
    }
    
    public TableModel getModel() {
        return dataModel;
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
            if (tableHeader != null) {
                tableHeader.setColumnModel(columnModel);
            }
            firePropertyChange("columnModel", old, columnModel);
            resizeAndRepaint();
        }
    }
    
    public TableColumnModel getColumnModel() {
        return columnModel;
    }
    
    public void setSelectionModel(ListSelectionModel newModel) {
        if (newModel == null) {
            throw new IllegalArgumentException("Cannot set a null SelectionModel");
        }
        ListSelectionModel oldModel = selectionModel;
        if (newModel != oldModel) {
            if (oldModel != null) {
                oldModel.removeListSelectionListener(this);
            }
            selectionModel = newModel;
            newModel.addListSelectionListener(this);
            firePropertyChange("selectionModel", oldModel, newModel);
            repaint();
        }
    }
    
    public ListSelectionModel getSelectionModel() {
        return selectionModel;
    }
    
    public void tableChanged(TableModelEvent e) {
        if (e == null || e.getFirstRow() == TableModelEvent.HEADER_ROW) {
            clearSelectionAndLeadAnchor();
            rowModel = null;
            if (getAutoCreateColumnsFromModel()) {
                createDefaultColumnsFromModel();
                return;
            }
            resizeAndRepaint();
            return;
        }
        if (rowModel != null) {
            repaint();
        }
        if (e.getType() == TableModelEvent.INSERT) {
            tableRowsInserted(e);
            return;
        }
        if (e.getType() == TableModelEvent.DELETE) {
            tableRowsDeleted(e);
            return;
        }
        int modelColumn = e.getColumn();
        int start = e.getFirstRow();
        int end = e.getLastRow();
        Rectangle dirtyRegion;
        if (modelColumn == TableModelEvent.ALL_COLUMNS) {
            dirtyRegion = new Rectangle(0, start * getRowHeight(), getColumnModel().getTotalColumnWidth(), 0);
        } else {
            int column = convertColumnIndexToView(modelColumn);
            dirtyRegion = getCellRect(start, column, false);
        }
        if (end != Integer.MAX_VALUE) {
            dirtyRegion.height = (end - start + 1) * getRowHeight();
            repaint(dirtyRegion.x, dirtyRegion.y, dirtyRegion.width, dirtyRegion.height);
        } else {
            clearSelectionAndLeadAnchor();
            resizeAndRepaint();
            rowModel = null;
        }
    }
    
    private void tableRowsInserted(TableModelEvent e) {
        int start = e.getFirstRow();
        int end = e.getLastRow();
        if (start < 0) {
            start = 0;
        }
        if (end < 0) {
            end = getRowCount() - 1;
        }
        int length = end - start + 1;
        selectionModel.insertIndexInterval(start, length, true);
        if (rowModel != null) {
            rowModel.insertEntries(start, length, getRowHeight());
        }
        int rh = getRowHeight();
        Rectangle drawRect = new Rectangle(0, start * rh, getColumnModel().getTotalColumnWidth(), (getRowCount() - start) * rh);
        revalidate();
        repaint(drawRect);
    }
    
    private void tableRowsDeleted(TableModelEvent e) {
        int start = e.getFirstRow();
        int end = e.getLastRow();
        if (start < 0) {
            start = 0;
        }
        if (end < 0) {
            end = getRowCount() - 1;
        }
        int deletedCount = end - start + 1;
        int previousRowCount = getRowCount() + deletedCount;
        selectionModel.removeIndexInterval(start, end);
        if (rowModel != null) {
            rowModel.removeEntries(start, deletedCount);
        }
        int rh = getRowHeight();
        Rectangle drawRect = new Rectangle(0, start * rh, getColumnModel().getTotalColumnWidth(), (previousRowCount - start) * rh);
        revalidate();
        repaint(drawRect);
    }
    
    public void columnAdded(TableColumnModelEvent e) {
        if (isEditing()) {
            removeEditor();
        }
        resizeAndRepaint();
    }
    
    public void columnRemoved(TableColumnModelEvent e) {
        if (isEditing()) {
            removeEditor();
        }
        resizeAndRepaint();
    }
    
    public void columnMoved(TableColumnModelEvent e) {
        if (isEditing()) {
            removeEditor();
        }
        repaint();
    }
    
    public void columnMarginChanged(ChangeEvent e) {
        if (isEditing()) {
            removeEditor();
        }
        TableColumn resizingColumn = getResizingColumn();
        if (resizingColumn != null && autoResizeMode == AUTO_RESIZE_OFF) {
            resizingColumn.setPreferredWidth(resizingColumn.getWidth());
        }
        resizeAndRepaint();
    }
    
    private int limit(int i, int a, int b) {
        return Math.min(b, Math.max(i, a));
    }
    
    public void columnSelectionChanged(ListSelectionEvent e) {
        boolean isAdjusting = e.getValueIsAdjusting();
        if (columnSelectionAdjusting && !isAdjusting) {
            columnSelectionAdjusting = false;
            return;
        }
        columnSelectionAdjusting = isAdjusting;
        if (getRowCount() <= 0 || getColumnCount() <= 0) {
            return;
        }
        int firstIndex = limit(e.getFirstIndex(), 0, getColumnCount() - 1);
        int lastIndex = limit(e.getLastIndex(), 0, getColumnCount() - 1);
        int minRow = 0;
        int maxRow = getRowCount() - 1;
        if (getRowSelectionAllowed()) {
            minRow = selectionModel.getMinSelectionIndex();
            maxRow = selectionModel.getMaxSelectionIndex();
            int leadRow = getAdjustedIndex(selectionModel.getLeadSelectionIndex(), true);
            if (minRow == -1 || maxRow == -1) {
                if (leadRow == -1) {
                    return;
                }
                minRow = maxRow = leadRow;
            } else {
                if (leadRow != -1) {
                    minRow = Math.min(minRow, leadRow);
                    maxRow = Math.max(maxRow, leadRow);
                }
            }
        }
        Rectangle firstColumnRect = getCellRect(minRow, firstIndex, false);
        Rectangle lastColumnRect = getCellRect(maxRow, lastIndex, false);
        Rectangle dirtyRegion = firstColumnRect.union(lastColumnRect);
        repaint(dirtyRegion);
    }
    
    public void valueChanged(ListSelectionEvent e) {
        boolean isAdjusting = e.getValueIsAdjusting();
        if (rowSelectionAdjusting && !isAdjusting) {
            rowSelectionAdjusting = false;
            return;
        }
        rowSelectionAdjusting = isAdjusting;
        if (getRowCount() <= 0 || getColumnCount() <= 0) {
            return;
        }
        int firstIndex = limit(e.getFirstIndex(), 0, getRowCount() - 1);
        int lastIndex = limit(e.getLastIndex(), 0, getRowCount() - 1);
        Rectangle firstRowRect = getCellRect(firstIndex, 0, false);
        Rectangle lastRowRect = getCellRect(lastIndex, getColumnCount() - 1, false);
        Rectangle dirtyRegion = firstRowRect.union(lastRowRect);
        repaint(dirtyRegion);
    }
    
    public void editingStopped(ChangeEvent e) {
        TableCellEditor editor = getCellEditor();
        if (editor != null) {
            Object value = editor.getCellEditorValue();
            setValueAt(value, editingRow, editingColumn);
            removeEditor();
        }
    }
    
    public void editingCanceled(ChangeEvent e) {
        removeEditor();
    }
    
    public void setPreferredScrollableViewportSize(Dimension size) {
        preferredViewportSize = size;
    }
    
    public Dimension getPreferredScrollableViewportSize() {
        return preferredViewportSize;
    }
    
    public int getScrollableUnitIncrement(Rectangle visibleRect, int orientation, int direction) {
        if (orientation == SwingConstants.HORIZONTAL) {
            return 100;
        }
        return getRowHeight();
    }
    
    public int getScrollableBlockIncrement(Rectangle visibleRect, int orientation, int direction) {
        if (orientation == SwingConstants.VERTICAL) {
            int rh = getRowHeight();
            return (rh > 0) ? Math.max(rh, (visibleRect.height / rh) * rh) : visibleRect.height;
        } else {
            return visibleRect.width;
        }
    }
    
    public boolean getScrollableTracksViewportWidth() {
        return !(autoResizeMode == AUTO_RESIZE_OFF);
    }
    
    public boolean getScrollableTracksViewportHeight() {
        return false;
    }
    
    protected boolean processKeyBinding(KeyStroke ks, KeyEvent e, int condition, boolean pressed) {
        boolean retValue = super.processKeyBinding(ks, e, condition, pressed);
        if (!retValue && condition == WHEN_ANCESTOR_OF_FOCUSED_COMPONENT && isFocusOwner() && !Boolean.FALSE.equals((Boolean)(Boolean)getClientProperty("JTable.autoStartsEdit"))) {
            Component editorComponent = getEditorComponent();
            if (editorComponent == null) {
                if (e == null || e.getID() != KeyEvent.KEY_PRESSED) {
                    return false;
                }
                int code = e.getKeyCode();
                if (code == KeyEvent.VK_SHIFT || code == KeyEvent.VK_CONTROL || code == KeyEvent.VK_ALT) {
                    return false;
                }
                int leadRow = getSelectionModel().getLeadSelectionIndex();
                int leadColumn = getColumnModel().getSelectionModel().getLeadSelectionIndex();
                if (leadRow != -1 && leadColumn != -1 && !isEditing()) {
                    if (!editCellAt(leadRow, leadColumn)) {
                        return false;
                    }
                }
                editorComponent = getEditorComponent();
                if (editorComponent == null) {
                    return false;
                }
            }
            if (editorComponent instanceof JComponent) {
                retValue = ((JComponent)(JComponent)editorComponent).processKeyBinding(ks, e, WHEN_FOCUSED, pressed);
                if (getSurrendersFocusOnKeystroke()) {
                    editorComponent.requestFocus();
                }
            }
        }
        return retValue;
    }
    
    private void setLazyValue(Hashtable h, Class c, String s) {
        h.put(c, new UIDefaults$ProxyLazyValue(s));
    }
    
    private void setLazyRenderer(Class c, String s) {
        setLazyValue(defaultRenderersByColumnClass, c, s);
    }
    
    protected void createDefaultRenderers() {
        defaultRenderersByColumnClass = new UIDefaults();
        setLazyRenderer(Object.class, "javax.swing.table.DefaultTableCellRenderer$UIResource");
        setLazyRenderer(Number.class, "javax.swing.JTable$NumberRenderer");
        setLazyRenderer(Float.class, "javax.swing.JTable$DoubleRenderer");
        setLazyRenderer(Double.class, "javax.swing.JTable$DoubleRenderer");
        setLazyRenderer(Date.class, "javax.swing.JTable$DateRenderer");
        setLazyRenderer(Icon.class, "javax.swing.JTable$IconRenderer");
        setLazyRenderer(ImageIcon.class, "javax.swing.JTable$IconRenderer");
        setLazyRenderer(Boolean.class, "javax.swing.JTable$BooleanRenderer");
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
    
    private void setLazyEditor(Class c, String s) {
        setLazyValue(defaultEditorsByColumnClass, c, s);
    }
    
    protected void createDefaultEditors() {
        defaultEditorsByColumnClass = new UIDefaults();
        setLazyEditor(Object.class, "javax.swing.JTable$GenericEditor");
        setLazyEditor(Number.class, "javax.swing.JTable$NumberEditor");
        setLazyEditor(Boolean.class, "javax.swing.JTable$BooleanEditor");
    }
    {
    }
    {
    }
    {
    }
    
    protected void initializeLocalVars() {
        setOpaque(true);
        createDefaultRenderers();
        createDefaultEditors();
        setTableHeader(createDefaultTableHeader());
        setShowGrid(true);
        setAutoResizeMode(AUTO_RESIZE_SUBSEQUENT_COLUMNS);
        setRowHeight(16);
        isRowHeightSet = false;
        setRowMargin(1);
        setRowSelectionAllowed(true);
        setCellEditor(null);
        setEditingColumn(-1);
        setEditingRow(-1);
        setSurrendersFocusOnKeystroke(false);
        setPreferredScrollableViewportSize(new Dimension(450, 400));
        ToolTipManager toolTipManager = ToolTipManager.sharedInstance();
        toolTipManager.registerComponent(this);
        setAutoscrolls(true);
    }
    
    protected TableModel createDefaultDataModel() {
        return new DefaultTableModel();
    }
    
    protected TableColumnModel createDefaultColumnModel() {
        return new DefaultTableColumnModel();
    }
    
    protected ListSelectionModel createDefaultSelectionModel() {
        return new DefaultListSelectionModel();
    }
    
    protected JTableHeader createDefaultTableHeader() {
        return new JTableHeader(columnModel);
    }
    
    protected void resizeAndRepaint() {
        revalidate();
        repaint();
    }
    
    public TableCellEditor getCellEditor() {
        return cellEditor;
    }
    
    public void setCellEditor(TableCellEditor anEditor) {
        TableCellEditor oldEditor = cellEditor;
        cellEditor = anEditor;
        firePropertyChange("tableCellEditor", oldEditor, anEditor);
    }
    
    public void setEditingColumn(int aColumn) {
        editingColumn = aColumn;
    }
    
    public void setEditingRow(int aRow) {
        editingRow = aRow;
    }
    
    public TableCellRenderer getCellRenderer(int row, int column) {
        TableColumn tableColumn = getColumnModel().getColumn(column);
        TableCellRenderer renderer = tableColumn.getCellRenderer();
        if (renderer == null) {
            renderer = getDefaultRenderer(getColumnClass(column));
        }
        return renderer;
    }
    
    public Component prepareRenderer(TableCellRenderer renderer, int row, int column) {
        Object value = getValueAt(row, column);
        boolean isSelected = false;
        boolean hasFocus = false;
        if (!isPrinting) {
            isSelected = isCellSelected(row, column);
            boolean rowIsLead = (selectionModel.getLeadSelectionIndex() == row);
            boolean colIsLead = (columnModel.getSelectionModel().getLeadSelectionIndex() == column);
            hasFocus = (rowIsLead && colIsLead) && isFocusOwner();
        }
        return renderer.getTableCellRendererComponent(this, value, isSelected, hasFocus, row, column);
    }
    
    public TableCellEditor getCellEditor(int row, int column) {
        TableColumn tableColumn = getColumnModel().getColumn(column);
        TableCellEditor editor = tableColumn.getCellEditor();
        if (editor == null) {
            editor = getDefaultEditor(getColumnClass(column));
        }
        return editor;
    }
    
    public Component prepareEditor(TableCellEditor editor, int row, int column) {
        Object value = getValueAt(row, column);
        boolean isSelected = isCellSelected(row, column);
        Component comp = editor.getTableCellEditorComponent(this, value, isSelected, row, column);
        if (comp instanceof JComponent) {
            JComponent jComp = (JComponent)(JComponent)comp;
            if (jComp.getNextFocusableComponent() == null) {
                jComp.setNextFocusableComponent(this);
            }
        }
        return comp;
    }
    
    public void removeEditor() {
        KeyboardFocusManager.getCurrentKeyboardFocusManager().removePropertyChangeListener("permanentFocusOwner", editorRemover);
        editorRemover = null;
        TableCellEditor editor = getCellEditor();
        if (editor != null) {
            editor.removeCellEditorListener(this);
            if (editorComp != null) {
                remove(editorComp);
            }
            Rectangle cellRect = getCellRect(editingRow, editingColumn, false);
            setCellEditor(null);
            setEditingColumn(-1);
            setEditingRow(-1);
            editorComp = null;
            repaint(cellRect);
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if (getUIClassID().equals(uiClassID)) {
            byte count = JComponent.getWriteObjCounter(this);
            JComponent.setWriteObjCounter(this, --count);
            if (count == 0 && ui != null) {
                ui.installUI(this);
            }
        }
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        if ((ui != null) && (getUIClassID().equals(uiClassID))) {
            ui.installUI(this);
        }
        createDefaultRenderers();
        createDefaultEditors();
        if (getToolTipText() == null) {
            ToolTipManager.sharedInstance().registerComponent(this);
        }
    }
    
    void compWriteObjectNotify() {
        super.compWriteObjectNotify();
        if (getToolTipText() == null) {
            ToolTipManager.sharedInstance().unregisterComponent(this);
        }
    }
    
    protected String paramString() {
        String gridColorString = (gridColor != null ? gridColor.toString() : "");
        String showHorizontalLinesString = (showHorizontalLines ? "true" : "false");
        String showVerticalLinesString = (showVerticalLines ? "true" : "false");
        String autoResizeModeString;
        if (autoResizeMode == AUTO_RESIZE_OFF) {
            autoResizeModeString = "AUTO_RESIZE_OFF";
        } else if (autoResizeMode == AUTO_RESIZE_NEXT_COLUMN) {
            autoResizeModeString = "AUTO_RESIZE_NEXT_COLUMN";
        } else if (autoResizeMode == AUTO_RESIZE_SUBSEQUENT_COLUMNS) {
            autoResizeModeString = "AUTO_RESIZE_SUBSEQUENT_COLUMNS";
        } else if (autoResizeMode == AUTO_RESIZE_LAST_COLUMN) {
            autoResizeModeString = "AUTO_RESIZE_LAST_COLUMN";
        } else if (autoResizeMode == AUTO_RESIZE_ALL_COLUMNS) {
            autoResizeModeString = "AUTO_RESIZE_ALL_COLUMNS";
        } else autoResizeModeString = "";
        String autoCreateColumnsFromModelString = (autoCreateColumnsFromModel ? "true" : "false");
        String preferredViewportSizeString = (preferredViewportSize != null ? preferredViewportSize.toString() : "");
        String rowSelectionAllowedString = (rowSelectionAllowed ? "true" : "false");
        String cellSelectionEnabledString = (cellSelectionEnabled ? "true" : "false");
        String selectionForegroundString = (selectionForeground != null ? selectionForeground.toString() : "");
        String selectionBackgroundString = (selectionBackground != null ? selectionBackground.toString() : "");
        return super.paramString() + ",autoCreateColumnsFromModel=" + autoCreateColumnsFromModelString + ",autoResizeMode=" + autoResizeModeString + ",cellSelectionEnabled=" + cellSelectionEnabledString + ",editingColumn=" + editingColumn + ",editingRow=" + editingRow + ",gridColor=" + gridColorString + ",preferredViewportSize=" + preferredViewportSizeString + ",rowHeight=" + rowHeight + ",rowMargin=" + rowMargin + ",rowSelectionAllowed=" + rowSelectionAllowedString + ",selectionBackground=" + selectionBackgroundString + ",selectionForeground=" + selectionForegroundString + ",showHorizontalLines=" + showHorizontalLinesString + ",showVerticalLines=" + showVerticalLinesString;
    }
    {
    }
    
    public boolean print() throws PrinterException {
        return print(JTable$PrintMode.FIT_WIDTH);
    }
    
    public boolean print(JTable$PrintMode printMode) throws PrinterException {
        return print(printMode, null, null);
    }
    
    public boolean print(JTable$PrintMode printMode, MessageFormat headerFormat, MessageFormat footerFormat) throws PrinterException {
        boolean showDialogs = !GraphicsEnvironment.isHeadless();
        return print(printMode, headerFormat, footerFormat, showDialogs, null, showDialogs);
    }
    
    public boolean print(JTable$PrintMode printMode, MessageFormat headerFormat, MessageFormat footerFormat, boolean showPrintDialog, PrintRequestAttributeSet attr, boolean interactive) throws PrinterException, HeadlessException {
        boolean isHeadless = GraphicsEnvironment.isHeadless();
        if (isHeadless) {
            if (showPrintDialog) {
                throw new HeadlessException("Can\'t show print dialog.");
            }
            if (interactive) {
                throw new HeadlessException("Can\'t run interactively.");
            }
        }
        if (isEditing()) {
            if (!getCellEditor().stopCellEditing()) {
                getCellEditor().cancelCellEditing();
            }
        }
        if (attr == null) {
            attr = new HashPrintRequestAttributeSet();
        }
        final PrinterJob job = PrinterJob.getPrinterJob();
        Printable printable = getPrintable(printMode, headerFormat, footerFormat);
        if (interactive) {
            printable = new JTable$ThreadSafePrintable(this, printable);
        }
        job.setPrintable(printable);
        if (showPrintDialog && !job.printDialog(attr)) {
            return false;
        }
        if (!interactive) {
            isPrinting = true;
            try {
                job.print(attr);
            } finally {
                isPrinting = false;
            }
            return true;
        }
        String progressTitle = UIManager.getString("PrintingDialog.titleProgressText");
        String dialogInitialContent = UIManager.getString("PrintingDialog.contentInitialText");
        MessageFormat statusFormat = new MessageFormat(UIManager.getString("PrintingDialog.contentProgressText"));
        String abortText = UIManager.getString("PrintingDialog.abortButtonText");
        String abortTooltip = UIManager.getString("PrintingDialog.abortButtonToolTipText");
        int abortMnemonic = UIManager.getInt("PrintingDialog.abortButtonMnemonic", -1);
        int abortMnemonicIndex = UIManager.getInt("PrintingDialog.abortButtonDisplayedMnemonicIndex", -1);
        final JButton abortButton = new JButton(abortText);
        abortButton.setToolTipText(abortTooltip);
        if (abortMnemonic != -1) {
            abortButton.setMnemonic(abortMnemonic);
        }
        if (abortMnemonicIndex != -1) {
            abortButton.setDisplayedMnemonicIndex(abortMnemonicIndex);
        }
        final JLabel statusLabel = new JLabel(dialogInitialContent);
        JOptionPane abortPane = new JOptionPane(statusLabel, JOptionPane.INFORMATION_MESSAGE, JOptionPane.DEFAULT_OPTION, null, new Object[]{abortButton}, abortButton);
        final JTable$ThreadSafePrintable wrappedPrintable = (JTable$ThreadSafePrintable)(JTable$ThreadSafePrintable)printable;
        wrappedPrintable.startUpdatingStatus(statusFormat, statusLabel);
        Container parentComp = getParent() instanceof JViewport ? getParent() : this;
        final JDialog abortDialog = abortPane.createDialog(parentComp, progressTitle);
        abortDialog.setDefaultCloseOperation(JDialog.DO_NOTHING_ON_CLOSE);
        final Action abortAction = new JTable$6(this, abortButton, abortDialog, statusLabel, wrappedPrintable, job);
        abortButton.addActionListener(abortAction);
        abortPane.getActionMap().put("close", abortAction);
        final WindowAdapter closeListener = new JTable$7(this, abortAction);
        abortDialog.addWindowListener(closeListener);
        printError = null;
        final Object lock = new Object();
        final PrintRequestAttributeSet copyAttr = attr;
        Runnable runnable = new JTable$8(this, job, copyAttr, lock, abortDialog, closeListener);
        Thread th = new Thread(runnable);
        th.start();
        abortDialog.setVisible(true);
        Throwable pe;
        synchronized (lock) {
            pe = printError;
            printError = null;
        }
        if (pe != null) {
            if (pe instanceof PrinterAbortException) {
                return false;
            } else if (pe instanceof PrinterException) {
                throw (PrinterException)(PrinterException)pe;
            } else if (pe instanceof RuntimeException) {
                throw (RuntimeException)(RuntimeException)pe;
            } else if (pe instanceof Error) {
                throw (Error)(Error)pe;
            }
            throw new AssertionError(pe);
        }
        return true;
    }
    
    public Printable getPrintable(JTable$PrintMode printMode, MessageFormat headerFormat, MessageFormat footerFormat) {
        return new TablePrintable(this, printMode, headerFormat, footerFormat);
    }
    {
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JTable$AccessibleJTable(this);
        }
        return accessibleContext;
    }
    {
    }
}
