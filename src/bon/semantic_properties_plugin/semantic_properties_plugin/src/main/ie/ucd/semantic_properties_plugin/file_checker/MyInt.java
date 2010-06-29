package ie.ucd.semantic_properties_plugin.file_checker;

public class MyInt implements MyObject {
	// making everything public for testing--- change later
	public MyInt() {
		id = "";
		value = 0;
	}

	public MyInt(String newId, long newValue) {
		id = newId;
		value = newValue;
	}

	private String id;
	private long value;

	public String getId() {
		return id;
	}

	public void setId(String id) {
		this.id = id;
	}

	public long getValue() {
		return value;
	}

	public void setValue(long value) {
		this.value = value;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof MyInt) {
			return toString().equals(obj.toString());
		}
		return false;
	}
	@Override
    public String toString() {
        return getId()+"="+getValue();
    }
	public MyObjectKind getKind() {
		return MyObjectKind.MyInt;
	}

	@Override
	public String getReg() {
		// TODO Auto-generated method stub
		return "<"+getId()+"=(+|-)(1-9)(0-9)+>";
	}

}
