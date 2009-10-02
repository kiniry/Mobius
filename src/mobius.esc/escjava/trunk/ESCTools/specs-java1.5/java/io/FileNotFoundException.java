package java.io;

public class FileNotFoundException extends IOException {
    
    public FileNotFoundException() {
        
    }
    
    public FileNotFoundException(String s) {
        super(s);
    }
    
    private FileNotFoundException(String path, String reason) {
        super(path + ((reason == null) ? "" : " (" + reason + ")"));
    }
}
