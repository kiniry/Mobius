package ie.ucd.semanticproperties.plugin.customobjects;

import java.net.URL;

public class MyURL extends MyObject {
	public MyURL() {
		super();
	}

	public MyURL(String newId, String newValue) {
		super(newId,newValue);
	}
	@Override
	public MyObjectKind getKind() {
		return MyObjectKind.URL;
	}
//	@Override
//	public String getReg() {
//		String urlid="((?:(?:http[s]?|ftp):\\/)?\\/?(?:[^:\\/\\s]+)(?:(?:\\/\\w+)*\\/)(?:[\\w\\-\\.]+[^#?\\s]+)(?:.*)?(?:#[\\w\\-]+)?)";
//		String urlid2="((?:mailto\\:|(?:news|(?:ht|f)tp(?:s?))\\://){1}\\S+)";
//		return urlid2;
//	}

}
