package java.net;

class URLConnection$1 implements FileNameMap {
    
    URLConnection$1() {
        
    }
    private FileNameMap map = URLConnection.access$000();
    
    public String getContentTypeFor(String fileName) {
        return map.getContentTypeFor(fileName);
    }
}
