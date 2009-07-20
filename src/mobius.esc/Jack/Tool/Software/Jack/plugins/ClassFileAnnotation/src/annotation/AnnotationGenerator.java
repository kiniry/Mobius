//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package annotation;

import jack.plugin.Generator;
import jack.plugin.JackJml2bConfiguration;
import jack.util.Logger;

import java.io.File;
import java.io.IOException;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.AField;
import jml2b.structure.java.Class;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.Parameters;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;

/**
 *
 *  @author L. Burdy
 **/
public class AnnotationGenerator extends Generator {

	String createdClass;
	
	
	public String getCreatedClass() {
		return createdClass;
	}
	public AnnotationGenerator(JackJml2bConfiguration config, Iterator compilation_units) {
		super(compilation_units);
		this.configuration = config;
	}

	public AnnotationGenerator(JackJml2bConfiguration config, ICompilationUnit c) {
		super(c, "Annotating class file");
		this.configuration = config;
	}
	

	private static boolean areEqual(
			IJml2bConfiguration config, 
		jml2b.structure.java.Type type,
		org.apache.bcel.generic.Type type2) {
		return type2.getSignature().equals(JmlConstantPool.getDescriptor(config, type));
	}

	/* (non-Javadoc)
	 * @see jack.plugin.Generator#coreRun(org.eclipse.core.runtime.IProgressMonitor, int, java.util.Vector)
	 */
	protected void coreRun(
		IProgressMonitor monitor,
		int file_count,
		Vector files) {
		monitor.subTask("Annotating class file");
		try {
			IdentifierResolver.init(configuration);

			for (int i = 0; i < file_count; ++i) {
				JmlFile jmlf = (JmlFile) files.get(i);
				Enumeration e = jmlf.getClasses();
				while (e.hasMoreElements()) {
					try {
						Class c = (Class) e.nextElement();
						SyntheticRepository sr =
							SyntheticRepository.getInstance(
								new ClassPath(
									ClassPath.getClassPath()
										+ ":"
										+ project.getWorkspace().getRoot().getLocation().toOSString()
										+ javaProject.getOutputLocation().toOSString()));
						sr.clear();
						JavaClass clazz =
							sr.loadClass(c.getFullyQualifiedName());
						JmlAttributes[] jmla = new JmlAttributes[5];
						JmlConstantPool jcp =
							new JmlConstantPool(clazz.getConstantPool());
						Vector fields = new Vector();
						Enumeration e1 = c.getFields();
						while (e1.hasMoreElements()) {
							AField f = (AField) e1.nextElement();
							if ((f.getModifiers()).isJml()) {
								fields.add(f);
								jcp.add(configuration, f);
							}
						}
						jmla[0] =
							new ModelFieldAttribute(
									configuration, 
								clazz.getConstantPool(),
								jcp,
								fields);
						Vector methods = new Vector();
						e1 = c.getMethods();
						while (e1.hasMoreElements()) {
							Method m = (Method) e1.nextElement();
							JmlAttributes[] jmlma =
								annotateMethod(m, clazz, jcp);
							if (((Modifiers) m.getModifiers()).isJml())
								methods.add(new JmlMethod(m, jmlma, jcp));
						}
						e1 = c.getConstructors();
						while (e1.hasMoreElements()) {
							Method m = (Method) e1.nextElement();
							annotateMethod(m, clazz, jcp);
						}
						jmla[1] =
							new ModelMethodAttribute(configuration,
								clazz.getConstantPool(),
								jcp,
								methods);
						jmla[2] =
							new InvariantAttribute(
								configuration,
								jcp,
								c,
								clazz.getConstantPool());
						jmla[3] =
							new ConstraintAttribute(
								configuration,
								jcp,
								c,
								clazz.getConstantPool());

						jmla[4] =
							new SecondConstantPoolAttribute(
								configuration,
								jcp,
								c,
								clazz.getConstantPool());

						Attribute aa[] = clazz.getAttributes();
						Attribute aa1[] = new Attribute[aa.length + 5];
						for (int j = 0; j < aa.length; j++)
							aa1[j] = aa[j];
						for (int j = 0; j < 5; j++)
							aa1[aa.length + j] = jmla[j];
						clazz.setAttributes(aa1);

						clazz.setConstantPool(jcp.getCompleteConstantPool());

						try {
							clazz.dump(
								new File(
									configuration.getSubdirectory(),
									(createdClass = clazz.getClassName().replace('.',File.separatorChar)) + ".class"));
						} catch (IOException ioe) {
							Logger.err.println(ioe.getMessage());
						}
					} catch (ClassNotFoundException cnfe) {
						Logger.get().println("Class not found");
						//TODO Remonter un message d'erreur
					} catch (JavaModelException cnfe) {
						Logger.get().println(cnfe.getMessage());
					}
					Logger.get().println("Done");
				}
			}
		} catch (Jml2bException e) {
			ErrorHandler.error((JmlFile) files.get(0), -1, -1, e.toString());
		} catch (RuntimeException re) {
			Logger.err.println(re.getStackTrace()[0].toString());
			Logger.err.println(re.toString());
		} finally {
			// free memory allocated for packages.
//			Package.clearAll();
		}

	}

	JmlAttributes[] annotateMethod(
		Method m,
		JavaClass clazz,
		JmlConstantPool jcp)
		throws Jml2bException {
		JmlAttributes[] jmlma = new JmlAttributes[4];
		org.apache.bcel.classfile.Method methodzz = null;
		org.apache.bcel.classfile.Method[] ma = clazz.getMethods();
		forl : for (int k = 0; k < ma.length; k++) {
			if (ma[k]
				.getName()
				.equals(m.isConstructor() ? "<init>" : m.getName())) {
				Vector margs = ((Parameters) m.getParams()).getSignature();
				org.apache.bcel.generic.Type[] targs = ma[k].getArgumentTypes();
				if (margs.size() == targs.length) {
					Enumeration en = margs.elements();
					int l = 0;
					while (en.hasMoreElements()) {
						Field element = (Field) en.nextElement();
						//TODO A tester
						if (!areEqual(configuration, element.getType(), targs[l++]))
							continue forl;
					}
					methodzz = ma[k];
				}
			}
		}
		try {
			jmlma[0] =
				new MethodSpecificationAttribute(
					configuration,
					jcp,
					clazz.getConstantPool(),
					m,
					methodzz);
			jmlma[1] =
				new AssertAttribute(
					configuration,
					jcp,
					clazz.getConstantPool(),
					m,
					methodzz);
			jmlma[2] =
				new LoopSpecificationAttribute(
					configuration,
					jcp,
					clazz.getConstantPool(),
					m,
					methodzz);
			jmlma[3] =
				new BlockSpecificationAttribute(
					configuration,
					jcp,
					clazz.getConstantPool(),
					m,
					methodzz);
		} catch (PogException pe) {
		}
		if (methodzz != null) {
			Attribute aa[] = methodzz.getAttributes();
			Attribute aa1[] = new Attribute[aa.length + 4];
			for (int j = 0; j < aa.length; j++)
				aa1[j] = aa[j];
			for (int j = 0; j < 4; j++)
				aa1[aa.length + j] = jmlma[j];
			methodzz.setAttributes(aa1);

		}
		return jmlma;
	}
}
