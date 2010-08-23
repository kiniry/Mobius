package ie.ucd.semanticproperties.plugin.customobjects;

public class Keyword {
	protected String keyword;
	protected String value;
	public Keyword() {
		keyword = "";
		value = "";
	}

	public Keyword(String key, String val) {
	  keyword = key;
    value = val;
	}

  public String getKeyword() {
    return keyword;
  }

  public String getValue() {
    return value;
  }

  @Override
  public String toString() {
      return getKeyword()+"="+getValue();
  }
}
