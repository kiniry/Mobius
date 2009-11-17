package java.sql;

public class DataTruncation extends SQLWarning {
    
    public DataTruncation(int index, boolean parameter, boolean read, int dataSize, int transferSize) {
        super("Data truncation", "01004");
        this.index = index;
        this.parameter = parameter;
        this.read = read;
        this.dataSize = dataSize;
        this.transferSize = transferSize;
        DriverManager.println("    DataTruncation: index(" + index + ") parameter(" + parameter + ") read(" + read + ") data size(" + dataSize + ") transfer size(" + transferSize + ")");
    }
    
    public int getIndex() {
        return index;
    }
    
    public boolean getParameter() {
        return parameter;
    }
    
    public boolean getRead() {
        return read;
    }
    
    public int getDataSize() {
        return dataSize;
    }
    
    public int getTransferSize() {
        return transferSize;
    }
    private int index;
    private boolean parameter;
    private boolean read;
    private int dataSize;
    private int transferSize;
}
