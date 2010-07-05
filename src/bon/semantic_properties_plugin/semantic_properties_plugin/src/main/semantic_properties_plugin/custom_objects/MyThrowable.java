package semantic_properties_plugin.custom_objects;

public class MyThrowable extends MyObject {
	public MyThrowable() {
		super();
	}

	public MyThrowable(String newId, Throwable newValue) {
		super(newId,newValue);
	}
	@Override
	public MyObjectKind getKind() {
		return MyObjectKind.Throwable;
	}
//	@Override
//	public String getReg() {
//		return "(\\w+\\.java)";
//	}

}
