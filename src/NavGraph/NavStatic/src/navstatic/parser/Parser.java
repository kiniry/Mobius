package navstatic.parser;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;

import navstatic.analyze.ConstructorRule;
import navstatic.analyze.CallRule;
import navstatic.analyze.RulePack;

import org.w3c.dom.Document;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;
import org.w3c.dom.Element;

import soot.Scene;
import soot.SootClass;
import soot.SootMethod;

public class Parser {
	final InputStream is;
	
	boolean debug = true;
	
	public Parser(InputStream is) {
		this.is = is;
	}
	
	public Parser() {
		is = this.getClass().getResourceAsStream("rules.xml");
	}
	
	static private SootMethod getMethod(Scene sc, String sign) {
		try {return sc.getMethod("<" + sign + ">");} catch (RuntimeException e) {return null;}
	}
	
	public RulePack parse(Scene sc) {
		XPathFactory xpf = XPathFactory.newInstance();
		DocumentBuilder db;
		XPath p = xpf.newXPath();
		RulePack pack = new RulePack();
		try {
			db = DocumentBuilderFactory.newInstance().newDocumentBuilder();
			db.setEntityResolver(new UriTransform());
			Document mainConfig = db.parse(is);

			NodeList nodes =
				(NodeList) p.evaluate("/navstatic/call", mainConfig, XPathConstants.NODESET);
			for(int i=0; i < nodes.getLength(); i++) {
				Element elt = (Element) (nodes.item(i));
				String ruleName = elt.getAttribute("name");
				String signature = elt.getAttribute("method");
				NodeList argsNodes =
					(NodeList) p.evaluate("argument", elt, XPathConstants.NODESET);
				ArrayList <Integer> args = new ArrayList<Integer>();
				for(int j=0; j < argsNodes.getLength(); j++) {
					Element elt2 = (Element) (argsNodes.item(j));
					Integer position = Integer.valueOf(elt2.getAttribute("position"));
					args.add(position);
				}
				
				SootMethod meth = getMethod(sc,signature);
				if (meth==null) {
					System.err.println("Cannot find method " + signature);
					continue;
				}
				CallRule rule = new CallRule (ruleName,meth,args);
				pack.callRules.add(rule);
			}

			nodes =
				(NodeList) p.evaluate("/navstatic/constructor", mainConfig, XPathConstants.NODESET);
			for(int i=0; i < nodes.getLength(); i++) {
				Element elt = (Element) (nodes.item(i));
				String ruleName = elt.getAttribute("name");
				String classname = elt.getAttribute("class");
				SootClass clazz = sc.getSootClass(classname);
				if (clazz == null) {
					System.err.println("Cannot find class " + classname);
					continue;
				}
				ConstructorRule rule = new ConstructorRule(ruleName, clazz);
				pack.constructorRules.add(rule);
			}

			nodes =
				(NodeList) p.evaluate("/navstatic/callback", mainConfig, XPathConstants.NODESET);
			for(int i=0; i < nodes.getLength(); i++) {
				Element elt = (Element) (nodes.item(i));
				String signature = elt.getAttribute("method");
				SootMethod meth = getMethod(sc,signature);
				if (meth==null) {
					System.err.println("Cannot find method " + signature);
					continue;
				}
				pack.callbackMethods.add(meth);
			}
			
			nodes =
				(NodeList) p.evaluate("/navstatic/tracked", mainConfig, XPathConstants.NODESET);
			for(int i=0; i < nodes.getLength(); i++) {
				Element elt = (Element) (nodes.item(i));
				String signature = elt.getAttribute("method");
				SootMethod meth = getMethod(sc,signature);
				if (meth==null) {
					System.err.println("Cannot find method " + signature);
					continue;
				}
				pack.trackedMethods.add(meth);
			}

			nodes =
				(NodeList) p.evaluate("/navstatic/setter", mainConfig, XPathConstants.NODESET);
			for(int i=0; i < nodes.getLength(); i++) {
				Element elt = (Element) (nodes.item(i));
				String signature = elt.getAttribute("method");
				SootMethod meth = getMethod(sc,signature);
				if (meth==null) {
					System.err.println("Cannot find method " + signature);
					continue;
				}
				pack.setterMethods.add(meth);
			}

			return pack;
		} catch (XPathExpressionException e) {
			assert false : "Correct statically defined xpath expressions.";
			e.printStackTrace();
			return null;
		} catch (IOException e) {
			System.err.println("IO problem with rule file: " + e.getMessage());
			e.printStackTrace();
			return null;
		} catch (SAXException e) {
			System.err.println("Syntax problem in rule file: " + e.getMessage());
			e.printStackTrace();
			return null;
		} catch (ParserConfigurationException e1) {
			assert false : "Simple XML parser setup.";
			e1.printStackTrace();
			return null;
		}

	}
			
}
