package java.net;

class Parts {
    String path;
    String query;
    String ref;
    
    Parts(String file) {
        
        int ind = file.indexOf('#');
        ref = ind < 0 ? null : file.substring(ind + 1);
        file = ind < 0 ? file : file.substring(0, ind);
        int q = file.lastIndexOf('?');
        if (q != -1) {
            query = file.substring(q + 1);
            path = file.substring(0, q);
        } else {
            path = file;
        }
    }
    
    String getPath() {
        return path;
    }
    
    String getQuery() {
        return query;
    }
    
    String getRef() {
        return ref;
    }
}
