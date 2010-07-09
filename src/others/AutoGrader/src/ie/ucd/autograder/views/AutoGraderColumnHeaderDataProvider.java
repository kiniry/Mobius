package ie.ucd.autograder.views;

import net.sourceforge.nattable.data.IDataProvider;

public class AutoGraderColumnHeaderDataProvider implements IDataProvider {

  private final AutoGraderDataProvider dataProvider;
  
  public AutoGraderColumnHeaderDataProvider(AutoGraderDataProvider dataProvider) {
    this.dataProvider = dataProvider;
  }

  public int getColumnCount() {
//    Log.info("Column header column count: " + dataProvider.getColumnCount());
    return dataProvider.getColumnCount();
  }

  public Object getDataValue(int columnIndex, int rowIndex) {
//    Log.info("Getting header value for col=" + columnIndex + ", row=" + rowIndex);
    return dataProvider.getColumnHeader(columnIndex);
  }

  public int getRowCount() {
//    Log.info("Getting column header row count (1)");
    return dataProvider.validData() ? 1 : 0;
  }

  public void setDataValue(int columnIndex, int rowIndex, Object newValue) {
    throw new UnsupportedOperationException();
  }

}
