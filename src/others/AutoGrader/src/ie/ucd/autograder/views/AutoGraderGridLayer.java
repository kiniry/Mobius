package ie.ucd.autograder.views;

import net.sourceforge.nattable.grid.layer.ColumnHeaderLayer;
import net.sourceforge.nattable.grid.layer.CornerLayer;
import net.sourceforge.nattable.grid.layer.GridLayer;
import net.sourceforge.nattable.grid.layer.RowHeaderLayer;
import net.sourceforge.nattable.layer.ILayer;
import net.sourceforge.nattable.layer.IUniqueIndexLayer;
import net.sourceforge.nattable.layer.stack.DefaultBodyLayerStack;
import net.sourceforge.nattable.selection.SelectionLayer;

public class AutoGraderGridLayer extends GridLayer {

  public AutoGraderGridLayer(IUniqueIndexLayer bodyDataLayer, IUniqueIndexLayer columnHeaderDataLayer, IUniqueIndexLayer rowHeaderDataLayer, IUniqueIndexLayer cornerDataLayer, boolean useDefaultConfiguration) {
    super(useDefaultConfiguration);
    init(bodyDataLayer, columnHeaderDataLayer, rowHeaderDataLayer, cornerDataLayer);
  }
  
  
  protected void init(IUniqueIndexLayer bodyDataLayer, IUniqueIndexLayer columnHeaderDataLayer, IUniqueIndexLayer rowHeaderDataLayer, IUniqueIndexLayer cornerDataLayer) {
    // Body
    DefaultBodyLayerStack bodyLayer = new DefaultBodyLayerStack(bodyDataLayer);
    
    SelectionLayer selectionLayer = bodyLayer.getSelectionLayer();

    // Column header
    ILayer columnHeaderLayer = new ColumnHeaderLayer(columnHeaderDataLayer, bodyLayer, selectionLayer);
    
    // Row header
    ILayer rowHeaderLayer = new RowHeaderLayer(rowHeaderDataLayer, bodyLayer, selectionLayer);
    
    // Corner
    ILayer cornerLayer = new CornerLayer(cornerDataLayer, rowHeaderLayer, columnHeaderLayer);
    
    setBodyLayer(bodyLayer);
    setColumnHeaderLayer(columnHeaderLayer);
    setRowHeaderLayer(rowHeaderLayer);
    setCornerLayer(cornerLayer);
  }
}
