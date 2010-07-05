package semantic_properties_plugin.custom_objects;

public class MyDescription extends MyObject {
	public MyDescription() {
		super();
	}

	public MyDescription(String newId, String newValue) {
		super(newId,newValue);
	}
	@Override
	public MyObjectKind getKind() {
		return MyObjectKind.Description;
	}
//	@Override
//	public String getReg() {
//		return "(.+?\\.)";
//	}

}
