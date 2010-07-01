package semantic_properties_plugin.custom_objects;

import java.util.Date;

public class MyDate extends MyObject {
	public MyDate() {
		super();
	}

	public MyDate(String newId, Date newValue) {
		super(newId,newValue);
	}
	@Override
	public MyObjectKind getKind() {
		return MyObjectKind.Date;
	}
	@Override
	public String getReg() {
		String digit="(\\d+)";
		return "<"+getId()+"="+digit+">";
	}

}
