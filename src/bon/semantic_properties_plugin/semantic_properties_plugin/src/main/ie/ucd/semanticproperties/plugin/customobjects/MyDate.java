package ie.ucd.semanticproperties.plugin.customobjects;

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
//	@Override
//	public String getReg() {
//		String digit="(\\d{1,2}(?:\\/|-)\\d{1,2}(?:\\/|-)\\d{4})";
//		return digit;
//	}

}
