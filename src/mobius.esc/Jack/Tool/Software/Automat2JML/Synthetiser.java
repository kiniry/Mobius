
import java.util.*;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

//Definition of the node type
import org.w3c.dom.Node;
import org.w3c.dom.Document;
import org.xml.sax.SAXException;


/*
 * Created on Mar 11, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

/**
 * @author tdupont
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */



//This class should synthesis properties out of the Xml Automata
public class Synthetiser {

	/*
	 * Fields declaration
	 * 
	 */
	//variables dedicated to the last file that has been processed
	private Document document;
	private String fileName;
	private LinkedList globalVariables; //List of Variables
	private LinkedList properties;		//List of Property
	private LinkedList instances;		//List of Properties instanciated, with MethodProperty attached to transitions
	private LinkedList system;			//List unused for now 
	
	
	//Complete list containing all files, properties, ..
	private LinkedList documents;		//List of the documents added to the class
	private LinkedList fileNames;		//List of the file names of the added document
	private LinkedList allGlobalVariables; //List of Variables
	private LinkedList allProperties;		//List of Property
	private LinkedList allInstances;		//List of Properties instanciated, with MethodProperty attached to transitions
	private LinkedList allSystem;			//List unused for now
	private boolean succeeded;
	private boolean isSynthetized;
	
	
	/*
	 * Constructor, edit the dom document
	 * 
	 */
	Synthetiser(String name){
		
		initNewDocument(name);
		
		System.err.println(name);
		
		succeeded = ParseDocument();
		if (succeeded == true ){
			documents.add(document);
			fileNames.add(fileName);
			allGlobalVariables = globalVariables; 
			allProperties = properties;
			allInstances = instances;
			allSystem    = system;
		}
		
	}

	
	/*
	 * 	Modifying functions
	 * 
	 */
	
	//add property files to be synthesized, if false : nothing had been added
	public boolean addPropertyFile(String name){

		boolean toBeAdded =false;
		
		initNewDocument(name);

		toBeAdded = ParseDocument();
		if (toBeAdded==true) {toBeAdded = checkDoubleEntry();
		/*System.out.println("Check function returned "+toBeAdded);*/}
		if (toBeAdded==true){
			//THE METHOD addAll should be tested to garanty the function
			documents.add(document);
			fileNames.add(fileName);
			toBeAdded = toBeAdded && allGlobalVariables.addAll(globalVariables); 
			toBeAdded = toBeAdded && allProperties.addAll(properties);			
			toBeAdded = toBeAdded && allInstances.addAll(instances);
			toBeAdded = toBeAdded && allSystem.addAll(system);
			isSynthetized = false;
			return toBeAdded;
		}
		
		return toBeAdded;
	}
	
	//synthesize the content of synthetizer
	public void synthesize(String directory, String pkgName, String propFileName){ 
		

		
		Iterator it,it2;
		LinkedList mpList = new LinkedList();
		LinkedList finalList = new LinkedList();
		Property prop;
		MethodProperty mp, mp2;
		LinkedList verifClassList = new LinkedList();
	
		String globalDefClass = "GlobalDefinitionClass";
		String packageString =  "package "+pkgName+" ; \n" ;
		directory = directory+"/"+pkgName;
		File outfile;
		FileOutputStream fwrite;

		Date date = new Date();
		String header = "\n/* Generated automatically on "+ date.toString()+"*/\n";

		
		it = allInstances.iterator();
		if (it.hasNext()){
			//there is something to synthetize
			prop = (Property) it.next();
			
			//Synthetize property classes
			it = allInstances.iterator();
			while (it.hasNext()){
				prop = (Property) it.next();

				//System.err.println("Iteration on allInstance: "+getPropClassName());
				outfile = new File(directory,prop.getPropClassName()+".java");
				if (outfile.exists()) {
					System.err.println("The file "+outfile.getName()+" already exists in "+outfile.getPath());
					if (! (outfile.canWrite())) System.err.println("The file cannot be written");
					else System.err.println("Nevertheless, the file could be written");
				}
				else {
					try{
						if (outfile.createNewFile()) {
							//System.err.println("New file created for "+outfile.getName());
							fwrite = new FileOutputStream(outfile);
							fwrite.write((header+"\n").getBytes());
							fwrite.write((packageString+"\n\n").getBytes());
							fwrite.write( prop.synthesizeAutomatonClass(globalVariables, globalDefClass).getBytes() );
							verifClassList.add(prop.getPropClassName());
						}
						else System.err.println("Unable to create new file called "+outfile.getName());
						try{
							mpList.addAll(prop.synthesizeMethods(globalVariables, globalDefClass))	;
						}catch(Exception e){ e.printStackTrace();}
					}catch(Exception e){System.err.println("Unable to create new file called "+outfile.getName());}
				}

			}
			
			//Synthetize global Declaration into a specific class
			outfile = new File(directory,globalDefClass+".java");
			if (outfile.exists()) {
				System.err.println("The file "+outfile.getName()+" already exists in "+outfile.getPath());
				if (! (outfile.canWrite())) System.err.println("The file cannot be written");
				else System.err.println("Nevertheless, the file could be written");
			}
			else {
				try{
					if (outfile.createNewFile()) {
						//System.err.println("New file created for "+outfile.getName());
						fwrite = new FileOutputStream(outfile);
						fwrite.write((header+"\n").getBytes());
						fwrite.write((packageString+"\n\n").getBytes());
						fwrite.write( prop.synthesizeGlobalClass(globalVariables, globalDefClass).getBytes() );
						verifClassList.add(globalDefClass);
					}
					else System.err.println("Unable to create new file called "+outfile.getName());
				}catch(Exception e){System.err.println("Unable to create new file called "+outfile.getName());}
			}	
			
		}		
		isSynthetized = true;
			
		
		//remove duplicate entry in mpList
		//System.err.println("Removing duplicated mp from the below list: ");
		mp = new MethodProperty("",""); 
		Collections.sort(mpList);
		it = mpList.iterator();
		while (it.hasNext()){
			mp2 = mp;
			mp = (MethodProperty) it.next(); 
			//System.err.println(mp);
			if (mp.compareTo(mp2)!= 0 ){finalList.add(mp);}
		}
		
		//Writing propFile
		String[] dotPropContent = MethodProperty.getDotPropContent(finalList);
		for(int i=0; i<dotPropContent.length  ; i++){
			outfile = new File(directory,propFileName+i+".prop");
			if (outfile.exists()) {
				System.err.println("The file "+outfile.getName()+" already exists in "+outfile.getPath());
				if (! (outfile.canWrite())) System.err.println("The file cannot be written");
				else System.err.println("Nevertheless, the file could be written");
				System.err.println("Nothing Done");
			}
			else {
				try{
					if (outfile.createNewFile()) {
						//System.err.println(dotPropContent[i-1]);
						fwrite = new FileOutputStream(outfile);
						fwrite.write((header+"\n").getBytes());
						for (int j=verifClassList.size() ; j>0; j--) {
							//System.err.println("writing class to import for verification");
							fwrite.write(("import "+pkgName+"."+verifClassList.get(j-1)+";\n").getBytes());
						}
						fwrite.write(("\n"+dotPropContent[i]+"\n\n").getBytes());
					}
					else System.err.println("Unable to create new file called "+outfile.getName());
				}catch(Exception e){System.err.println("Unable to create new file called "+outfile.getName());}
			}	
			
		}
		
		
		String[] updateContent = MethodProperty.getUpdateActions(finalList);
		for(int i=0 ; i<updateContent.length ; i++){
			outfile = new File(directory,propFileName+i+".body");
			if (outfile.exists()) {
				System.err.println("The file "+outfile.getName()+" already exists in "+outfile.getPath());
				if (! (outfile.canWrite())) System.err.println("The file cannot be written");
				else System.err.println("Nevertheless, the file could be written");
				System.err.println("Nothing Done");
			}
			else {
				try{
					if (outfile.createNewFile()) {
						//System.err.println(updateContent[i-1]);
						fwrite = new FileOutputStream(outfile);
						fwrite.write((header+"\n").getBytes());
						fwrite.write((updateContent[i]+"\n\n").getBytes());
					}
					else System.err.println("Unable to create new file called "+outfile.getName());
				}catch(Exception e){System.err.println("Unable to create new file called "+outfile.getName());}
			}	
			
		}
		
				
	}
	
	
	
	
	/*
	 * 	Modifying functions
	 * 
	 */
	
	//prepare fields to add a new file property
	private void initNewDocument(String name){
		fileName = name;
		documents = new LinkedList();
		fileNames = new LinkedList();
		globalVariables = new LinkedList();
		properties= new LinkedList();
		instances = new LinkedList();
		system    = new LinkedList();
		isSynthetized=false;
		
	}
	//parse the file document and call buildDataStructure
	private boolean ParseDocument(){
		
		boolean isValid=false;
		
		//Parse XML Document
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setValidating(true);
		//factory.setNamespaceAware(true);
		try {
			DocumentBuilder builder = factory.newDocumentBuilder();
			document = builder.parse(new File(fileName));
			System.err.println("\tParsing succeeded");
			isValid=this.buildDataStructure();
			return isValid;
		} catch (SAXException sxe) {
			// Error generated during parsing)
			Exception x = sxe;
			if (sxe.getException() != null)
				x = sxe.getException();
			x.printStackTrace();

		} catch (ParserConfigurationException pce) {
			// Parser with specified options can't be built
			pce.printStackTrace();

		} catch (IOException ioe) {
			// I/O error
			ioe.printStackTrace();
		}	
		return false;
	}
	//build the data structures in the temporary fields dedicated to it
	private boolean buildDataStructure() {
		
		Node child, node = document;
		Outils o = Outils.outilsFactory();
		String name, value, type;
		Property prop;
		boolean found = false;
		int i;
		
		
		//skip doctype,... and search for the NTA tag
		i = 0 ;
		while (i < o.childCount(document) && found == false){
			node = o.child(document, i); 
			if  ( (o.Name(node).toLowerCase().compareTo("nta") == 0)
					&&  (o.Type(node).toLowerCase().compareTo("element") == 0 ) )
					{ found = true;}
			i++;
		}
		if (found == false) { return false;}

		//For all children of NTA
		for (i=0 ; i < o.childCount(node) ; i++)
		{
			child = o.child(node, i);			
			name = o.Name(child).toLowerCase();
			type = o.Type(child).toLowerCase();
			value = o.Value(child);
			
			if (type.compareTo("element") == 0  ){
				//Extraction of the Global declaration
				if ( name.compareTo("declaration")==0 ){
					//o.displayNodeInformation(2, child);//simple print	
					globalVariables = o.extractDeclaration(child);
					if (globalVariables != null) { 
						System.err.println("\t\tGlobal Variable extracted");}//*/
				}
				
				//Extraction of templates
				if (name.compareTo("template")==0 ){
					//o.displayFrom( 0 , child);//simple print	
					prop = new Property(child);
					if (prop.isSynthetizable()) {
						properties.add(prop); //might not be a GoodProperty			
						System.out.println("\t\tAdded new property "+prop.getPropClassName());
					}
					else { System.out.println("Synthesis failed while analysing <template> .. </template> content"); return false;}
				}
				
				//Extraction of instances
				if (name.compareTo("instantiation")==0 ){
					//o.displayNodeInformation(2, child);//simple print	
					System.err.println("\t\tStarting properties's instanciation");
					instances = o.extractInstances(child, properties);
					//if (extractInstances(child) == false ) {System.err.println("Instances extraction failed");}
					System.err.println("\t\tProperties instanciated");
				}	
				
				//Extraction of system : may always be useless
				if (name.compareTo("system")==0 ) {
					//o.displayNodeInformation(2, child);//simple print	
					o.extractSystem(child);
				}
				
			}
		
		}
	
		return true;
		
	}
	//verify the compatibility if no double would be inserted before merging variable list
	//used when a new file xml files is added to the properties
	private boolean checkDoubleEntry(){
		
		
		//TODO should also check instantiation names and not only global variables
		
		
		Variables var1,var2;
		Iterator it1= globalVariables.iterator();
		Iterator it2= allGlobalVariables.iterator();
		
		//sort the 2 lists of Global variable (ascending)
		Collections.sort(globalVariables);   
		Collections.sort(allGlobalVariables);
		
		if (! (it1.hasNext())) return true;
		if (! (it2.hasNext())) return true;
		var1=(Variables)it1.next();
		var2=(Variables)it2.next();
		while (it1.hasNext() || it2.hasNext() ){
						
			while(var1.compareTo(var2) > 0 ){
				if (it2.hasNext()) var2 = (Variables)it2.next() ;
				else return true; //The entire list had been scanned and no double entry had been found
			}
			while(var1.compareTo(var2) < 0) {
				if (it1.hasNext()) var1 = (Variables)it1.next() ;
				else return true; //The entire list had been scanned and no double entry had been found
			}
			if (var1.compareTo(var2) == 0) return false;//Double entry found
		}
		
		//just in case lists had only one element each
		return (var1.compareTo(var2) != 0);
	}
	
	
	/*
	 * 	Access function
	 * 
	 */
		
	//if tells if the synthesis can be proceed
	public boolean isSynthesizable() {return succeeded;}
	//return the list of file names (String) added that the synthesis would proceed
	public LinkedList getFileList() {return fileNames;}
	//return after property synthesis, a list of methodProperty 
	
	
	
	//Display function
	public void displayXMLTree(){
		
		Node child;
		Outils o = Outils.outilsFactory();
		
		//Affichage des proprietes de la racine
		System.out.println( "*** Affichage de l'arbre XML complet   ***\n");
		System.out.println( "Type is:  " + o.Type(document)  );
		System.out.println( "Name is:  " + o.Name(document)  );		
		System.out.println( "Value is: " +o.Value(document)  );
		
		//display attributes here
		System.out.println( "There are " + o.attributeCount(document) 
				+ " Attributes");
		
		System.out.println( "There are " + o.childCount(document) + "Nodes ");
		for (int i=0 ; i< o.childCount(document) ; i++)
		{
			child = o.child(document, i);
			o.displayFrom(1 , child);
		}
	
	}
	public String getGlobalVariables(){ 
	
		String string="Avant sort\n";
		Iterator iter = allGlobalVariables.iterator();
		while (iter.hasNext()){ string += iter.next().toString()+"\n";}
		
		Collections.sort(allGlobalVariables);
		
		string += "Apres sort\n";
		iter = allGlobalVariables.iterator();
		while (iter.hasNext()){ string += iter.next().toString()+"\n";}
		
		return string;
	}
	
	
	
	
	
	
	
	

	
}