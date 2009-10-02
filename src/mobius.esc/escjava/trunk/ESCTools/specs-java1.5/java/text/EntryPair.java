package java.text;

final class EntryPair {
    public String entryName;
    public int value;
    public boolean fwd;
    
    public EntryPair(String name, int value) {
        this(name, value, true);
    }
    
    public EntryPair(String name, int value, boolean fwd) {
        
        this.entryName = name;
        this.value = value;
        this.fwd = fwd;
    }
}
