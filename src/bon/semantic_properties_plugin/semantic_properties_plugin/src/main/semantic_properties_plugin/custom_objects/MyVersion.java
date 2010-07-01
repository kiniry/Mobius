package semantic_properties_plugin.custom_objects;

public class MyVersion extends MyObject {
	public MyVersion() {
		super();
	}

	public MyVersion(String newId, float newValue) {
		super(newId,newValue);
	}
	@Override
	public MyObjectKind getKind() {
		return MyObjectKind.Version;
	}
	@Override
	public String getReg() {
		return "<"+getId()+"=([0-9](?:.[0-9])*)>";
	}

}
