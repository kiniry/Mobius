package ie.ucd.semanticproperties.plugin.customobjects;

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
//	@Override
//	public String getReg() {
//		String emailid="([\\w-\\.]+@(:?[\\w-]+\\.)+[\\w-]{2,4}$)";
//		return emailid;
//	}

}
