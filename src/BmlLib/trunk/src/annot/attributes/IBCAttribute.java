package annot.attributes;

import annot.io.AttributeWriter;

public interface IBCAttribute {
	public String getName();

	public void save(AttributeWriter aw);

	public int getIndex();

}
