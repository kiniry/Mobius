package semantic_properties_plugin.custom_objects;

public class MyObject {
	protected String id;
	protected Object value;	
	public MyObject() {
		id = "";
		value = 0;
	}

	public MyObject(String newId, Object newValue) {
		id = newId;
		value = newValue;
	}

	public String getId() {
		return id;
	}

	public void setId(String id) {
		this.id = id;
	}

	public Object getValue() {
		return value;
	}

	public void setValue(Object value) {
		this.value = value;
	}
	@Override
    public String toString() {
        return getId()+"="+getValue();
    }
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof MyObject) {
			return toString().equals(obj.toString());
		}
		return false;
	}
	
	public MyObjectKind getKind() {
		return MyObjectKind.unknown;
	}

	public String getReg() {
		return "<"+getId()+"=)>";
	}

}
