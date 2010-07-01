package semantic_properties_plugin.custom_objects;

public class MyString extends MyObject {
	public MyString() {
		super();
	}

	public MyString(String newId, String newValue) {
		super(newId,newValue);
	}
	@Override
	public MyObjectKind getKind() {
		return MyObjectKind.String;
	}
	@Override
	public String getReg() {
		return "<"+getId()+"=(.+)>";
	}

}
