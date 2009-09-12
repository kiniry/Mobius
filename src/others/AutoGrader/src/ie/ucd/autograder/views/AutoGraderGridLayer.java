package ie.ucd.autograder.views;

import net.sourceforge.nattable.grid.layer.CornerLayer;
import net.sourceforge.nattable.grid.layer.DimensionallyDependentLayer;
import net.sourceforge.nattable.grid.layer.GridLayer;
import net.sourceforge.nattable.layer.ILayer;
import net.sourceforge.nattable.layer.IUniqueIndexLayer;
import net.sourceforge.nattable.layer.config.DefaultColumnHeaderStyleConfiguration;
import net.sourceforge.nattable.viewport.ViewportLayer;

public class AutoGraderGridLayer extends GridLayer {

  public AutoGraderGridLayer(IUniqueIndexLayer bodyDataLayer, IUniqueIndexLayer columnHeaderDataLayer, IUniqueIndexLayer rowHeaderDataLayer, IUniqueIndexLayer cornerDataLayer, boolean useDefaultConfiguration) {
    super(useDefaultConfiguration);
    init(bodyDataLayer, columnHeaderDataLayer, rowHeaderDataLayer, cornerDataLayer);
  }
  
  
  protected void init(IUniqueIndexLayer bodyDataLayer, IUniqueIndexLayer columnHeaderDataLayer, IUniqueIndexLayer rowHeaderDataLayer, IUniqueIndexLayer cornerDataLayer) {
    // Body
    ViewportLayer bodyLayer = new ViewportLayer(bodyDataLayer);
    // Column header
    DimensionallyDependentLayer columnHeaderLayer = new DimensionallyDependentLayer(columnHeaderDataLayer, bodyLayer, columnHeaderDataLayer);
    columnHeaderLayer.addConfiguration(new DefaultColumnHeaderStyleConfiguration());
    // Row header
    ILayer rowHeaderLayer = new DimensionallyDependentLayer(rowHeaderDataLayer, rowHeaderDataLayer, bodyLayer);
    // Corner
    ILayer cornerLayer = new CornerLayer(cornerDataLayer, rowHeaderLayer, columnHeaderLayer);
    
    setBodyLayer(bodyLayer);
    setColumnHeaderLayer(columnHeaderLayer);
    setRowHeaderLayer(rowHeaderLayer);
    setCornerLayer(cornerLayer);
  }
}
