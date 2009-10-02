package java.text;

interface Format$FieldDelegate {
    
    public void formatted(Format$Field attr, Object value, int start, int end, StringBuffer buffer);
    
    public void formatted(int fieldID, Format$Field attr, Object value, int start, int end, StringBuffer buffer);
}
