package ie.ucd.autograder.views;

import net.sourceforge.nattable.data.IDataProvider;


public final class EmptyDataProvider implements IDataProvider {

  public int getColumnCount() {
    return 0;
  }

  public Object getDataValue(int columnIndex, int rowIndex) {
    return null;
  }

  public int getRowCount() {
    return 0;
  }

  public void setDataValue(int columnIndex, int rowIndex, Object newValue) {
    throw new UnsupportedOperationException();
  }



}
