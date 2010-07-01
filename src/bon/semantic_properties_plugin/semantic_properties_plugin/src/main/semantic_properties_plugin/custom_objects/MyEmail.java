package semantic_properties_plugin.custom_objects;

import java.util.Date;

public class MyEmail extends MyObject {
	public MyEmail() {
		super();
	}

	public MyEmail(String newId, String newValue) {
		super(newId,newValue);
	}
	@Override
	public MyObjectKind getKind() {
		return MyObjectKind.Email;
	}
	@Override
	public String getReg() {
		String emailid="(\\w+@\\w+\\.(:?com|ie))";
		return "<"+getId()+"="+emailid+">";
	}

}
