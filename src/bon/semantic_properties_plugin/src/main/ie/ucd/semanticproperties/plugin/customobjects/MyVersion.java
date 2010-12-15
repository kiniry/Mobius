package ie.ucd.semanticproperties.plugin.customobjects;

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
//	@Override
//	public String getReg() {
//		return "([0-9](?:.[0-9])*)";
//	}

}
