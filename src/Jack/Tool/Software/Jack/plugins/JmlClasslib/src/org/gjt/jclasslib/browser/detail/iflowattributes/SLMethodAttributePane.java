/*
 * Created on January 19, 2005
 *
 */
package org.gjt.jclasslib.browser.detail.iflowattributes;


import javax.swing.table.TableColumn;
import javax.swing.table.TableColumnModel;
import javax.swing.tree.TreePath;
import org.gjt.jclasslib.browser.BrowserServices;
import org.gjt.jclasslib.browser.detail.ListDetailPane.ColumnCache;
import org.gjt.jclasslib.browser.detail.attributes.AbstractAttributeListDetailPane;
import org.gjt.jclasslib.browser.detail.attributes.AbstractAttributeTableModel;
import org.gjt.jclasslib.structures.AttributeInfo;
import org.gjt.jclasslib.structures.iflowattributes.SecLevelMethodAttribute;
import org.gjt.jclasslib.structures.iflowattributes.Util;


/**
 *
 *  @author Luca Martini
 **/
public class SLMethodAttributePane extends AbstractAttributeListDetailPane {
    
    /**
       Constructor.
       @param services the associated browser services.
    */
    public SLMethodAttributePane(BrowserServices services) {
	super(services);
    }
   
    public void show(TreePath treePath) {
	    super.show(treePath);
	    TableColumnModel tcm = getTableColumnModel();
	    System.out.println(tcm);
	    
	    TableColumn tc = tcm.getColumn(0);
	    int width = getColumnWidth(0);
	    tc.setWidth(width);
	    tc.setPreferredWidth(width);
    }
	    
    protected AbstractAttributeTableModel createTableModel(AttributeInfo attribute) {
        return new AttributeTableModel(attribute);
    }

    private class AttributeTableModel extends AbstractAttributeTableModel {
	
        private static final int COLUMN_COUNT = 2;
        
        private static final int REGISTER_COLUMN_INDEX = 0;
        private static final int SEC_LEVEL_COLUMN_INDEX = 1;
        
        private static final int REGISTER_COLUMN_WIDTH = 150;
        private static final int SEC_LEVEL_COLUMN_WIDTH = 150;

	private static final int EFFECT_OFFSET = 0;
	private static final int EXCEFFECT_OFFSET = 1;
	private static final int IMPL_PAR_OFFSET = 2;	
	private static final int RETURN_VALUE_OFFSET = 3;
	private static final int REGISTER_OFFSET = 4;

	private ColumnCache columnCache;
	
	private SecLevelMethodAttribute slm_attribute;
        String[] levels;

	private AttributeTableModel(AttributeInfo attribute) {
            super(attribute);
	    slm_attribute = (SecLevelMethodAttribute) attribute;
	    byte[] regs = slm_attribute.getRegisters(); 
	    levels = new String[regs.length+REGISTER_OFFSET];
	    levels[EFFECT_OFFSET] = Util.secLeveByte2String(slm_attribute.getEffect());
	    levels[EXCEFFECT_OFFSET] = Util.secLeveByte2String(slm_attribute.getExceffect());
	    levels[IMPL_PAR_OFFSET] = Util.secLeveByte2String(slm_attribute.getImpl_Par());
	    levels[RETURN_VALUE_OFFSET] = Util.secLeveByte2String(slm_attribute.getReturn_value());
	    int j = REGISTER_OFFSET;
	    for (int i = 0; i < regs.length; i++,j++) {
		levels[j] = Util.secLeveByte2String(regs[i])+(slm_attribute.isArray(i)?"[]":"");
	    }
	    
	}
        
	
        public int getColumnWidth(int column) {
	    switch (column) {
 	    case REGISTER_COLUMN_INDEX:
 		return REGISTER_COLUMN_WIDTH;
 	    case SEC_LEVEL_COLUMN_INDEX:
 		return SEC_LEVEL_COLUMN_WIDTH;
 	    default:
 		return 1000;
 		//return NUMBER_COLUMN_WIDTH;
             }
	}
        
        public int getRowCount() {
            return slm_attribute.getRegisters().length+REGISTER_OFFSET;
        }
        
        public int getColumnCount() {
            return COLUMN_COUNT;
        }
    
	public String getColumnName(int column) {
	    return doGetColumnName(column);
	}
    
        protected String doGetColumnName(int column) {
            switch (column) {
	    case REGISTER_COLUMN_INDEX:
		return "Register";
	    case SEC_LEVEL_COLUMN_INDEX:
		return "Sec. Level";
	    default:
		return "";
            }
        }
        
        protected Class doGetColumnClass(int column) {
            return Number.class;
        }
        
	public Object getValueAt(int row, int column) {
	    if (columnCache == null) {
		columnCache = new ColumnCache(getRowCount(), getColumnCount());
	    }
	    
	    Object value = columnCache.getValueAt(row, column);
	    if (value == null) {
		value = doGetValueAt(row, column);
		columnCache.setValueAt(row, column, value);
	    }
	    
	    return value;
	}
	
	protected Object doGetValueAt(int row, int column) {
            switch (column) {
	    case SEC_LEVEL_COLUMN_INDEX:
		return levels[row];
	    case REGISTER_COLUMN_INDEX:
		if (row>=REGISTER_OFFSET) 
		    return String.valueOf(row - REGISTER_OFFSET);
		switch (row) {
		case EFFECT_OFFSET:
		    return "Heap Effect";
		
		case EXCEFFECT_OFFSET:
		    return "Exc. Effect"; 

		case IMPL_PAR_OFFSET:
		    return "Implicit";

		case RETURN_VALUE_OFFSET:
		    return "Return Value";
  
		default:
		    return "";
		}
		
	    default:
		return "";
            }
        }
    }
}
