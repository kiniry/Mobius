package ie.ucd.semanticproperties.plugin.customobjects;

public class MyString extends MyStringObject {
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
//	@Override
//	public String getReg() {
//		return "(\\S+)";
//	}

}
