/*
 * This file is part of the JML2 Eclipse Plug-in Project.
 *
 * Copyright (C) 2003-2008 Swiss Federal Institute of Technology Zurich
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * Paolo Bazzi, Summer 2006
 *
 */

package ch.ethz.inf.pm.jml.plugin;

import org.eclipse.core.resources.IFile;

/**
 * @author Paolo Bazzi
 *
 */
public class JmlErrorElement {

	private final int lineNr;
	private final int charNr;
	private final String message;
	private final IFile file;
	private final String jmlReference;

	public JmlErrorElement(int lineNr, int charNr, String message, IFile file,
			String jmlReference) {
		this.message = message;
		this.lineNr = lineNr;
		this.charNr = charNr;
		this.file = file;
		this.jmlReference = jmlReference;
	}

	public IFile getFile() {
		return file;
	}

	public String getJmlReference() {
		return jmlReference;
	}

	public String getMessage() {
		return message;
	}

	public int getLineNr() {
		return lineNr;
	}

	public int getCharNr() {
		return charNr;
	}

	@Override
	public String toString() {
		StringBuffer buf = new StringBuffer();
		buf.append("File=" + file.getName() + ", ");
		buf.append("Line= " + lineNr + ", ");
		buf.append("Char=" + charNr  + ", ");
		buf.append("Message= " + message  + ", ");
		buf.append("JML Reference= " + jmlReference);
		return buf.toString();
	}
}

