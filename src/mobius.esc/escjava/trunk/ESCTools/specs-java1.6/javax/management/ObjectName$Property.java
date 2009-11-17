package javax.management;

final class ObjectName$Property {
    int _key_index;
    int _key_length;
    int _value_length;
    
    ObjectName$Property(int key_index, int key_length, int value_length) {
        
        _key_index = key_index;
        _key_length = key_length;
        _value_length = value_length;
    }
    
    void setKeyIndex(int key_index) {
        _key_index = key_index;
    }
    
    String getKeyString(String name) {
        return name.substring(_key_index, _key_index + _key_length);
    }
    
    String getValueString(String name) {
        int in_begin = _key_index + _key_length + 1;
        int out_end = in_begin + _value_length;
        return name.substring(in_begin, out_end);
    }
}
