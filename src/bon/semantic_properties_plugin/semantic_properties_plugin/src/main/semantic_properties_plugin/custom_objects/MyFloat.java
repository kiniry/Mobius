package semantic_properties_plugin.custom_objects;

public class MyFloat extends MyObject {
	public MyFloat(String newId,float newValue) {
		super(newId,newValue);
	}
	public MyFloat() {
		super("",(float) 0.0);
	}
	@Override
	public MyObjectKind getKind() {
		return MyObjectKind.MyFloat;
	}
//	@Override
//	public String getReg() {
//		return "([-+]?\\d*\\.?\\d*)";
//	}

}
