/*
 *
 * Copyright (C) 2005  brad kyer b.kyer _at_ hydrogenline.com
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package org.apache.tools.ant.taskdefs;

import java.util.List;
import java.util.ArrayList;

/**
 * Merge/Diff helper functions
 *
 * @author Brad G. Kyer
 *         <a href="mailto:b.kyer _at_ hydrogenline.com">b.kyer _at_ hydrogenline.com</a>
 *
 * @version $Revision: 1.0.0 $
 *
 * @since Ant 1.5.1
 *
 * @ant.task category="utility"
 */
class MergeDiffHelper {

    private static final String DIFF_TYPE_ED      = "-e";
    private static final String DIFF_TYPE_CONTEXT = "-c";
    private static final String DIFF_TYPE_UNIFIED = "-u";
    private static final String DIFF_TYPE_NORMAL  = "-n";
    private static final String DIFF_TYPE_DEFAULT = DIFF_TYPE_CONTEXT;

    private static       List   TYPES;

    static {
        TYPES = new ArrayList();
        TYPES.add(DIFF_TYPE_ED);
        TYPES.add(DIFF_TYPE_CONTEXT);
        TYPES.add(DIFF_TYPE_UNIFIED);
        TYPES.add(DIFF_TYPE_NORMAL);
    }

    public static final String checkDiffType(String aType) {
        String myType = null;
        
        if(aType != null) {
            if(TYPES.contains(aType)) {
                myType = aType;
            }
        }

        if(myType == null) {
            myType = DIFF_TYPE_DEFAULT;
        }
        return(myType);
    }


    private MergeDiffHelper () {
        super();
    }

}
