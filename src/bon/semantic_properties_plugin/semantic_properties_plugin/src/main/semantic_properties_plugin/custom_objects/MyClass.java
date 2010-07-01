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
	@Override
	public String getReg() {
		String clazz="(\\w+.class)";
		return "<"+getId()+"="+clazz+">";
	}

}
