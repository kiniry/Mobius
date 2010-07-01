package semantic_properties_plugin.custom_objects;

public class MyExpression extends MyObject {
	public MyExpression() {
		super();
	}

	public MyExpression(String newId, String newValue) {
		super(newId,newValue);
	}
	@Override
	public MyObjectKind getKind() {
		return MyObjectKind.Expression;
	}
	@Override
	public String getReg() {
		return "<"+getId()+"=(.+)>";
	}

}
