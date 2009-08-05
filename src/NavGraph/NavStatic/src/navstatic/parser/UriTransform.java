package navstatic.parser;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.net.URISyntaxException;

import org.xml.sax.EntityResolver;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

/**
 * This class resolves the only DTD used 
 * @author piac6784
 *
 */
public class UriTransform implements EntityResolver {
	
	UriTransform() { }
	
	@Override
	public InputSource resolveEntity(String publicId, String systemId)
			throws SAXException, IOException {
		
		File file;
		String dtd;
		try {
			file = new File(new URI(systemId).getPath());
			dtd = file.getName();
		} catch (URISyntaxException e) {
			throw new IOException("Bad URI: " + e.getMessage());
		}
		InputStream is = 
			(dtd.equals("rules.dtd")) ? this.getClass().getResourceAsStream("rules.dtd") : new FileInputStream(file);
		return new InputSource(is);
	}

}
