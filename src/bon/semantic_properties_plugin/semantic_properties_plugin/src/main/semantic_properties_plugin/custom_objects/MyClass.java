package semantic_properties_plugin.custom_objects;

public class MyClass extends MyObject {
	public MyClass() {
		super();
	}

	public MyClass(String newId, Class<?> newValue) {
		super(newId,newValue);
	}
	@Override
	public MyObjectKind getKind() {
		return MyObjectKind.Class;
	}
//	@Override
//	public String getReg() {
//		String clazz1="([a-zA-Z](?:[a-zA-Z0-9])*(?:[\\.][a-zA-Z](?:[a-zA-Z0-9])*)*)";
//		//String clazz="(\\w+.class)";
//		return clazz1;
//	}

}
