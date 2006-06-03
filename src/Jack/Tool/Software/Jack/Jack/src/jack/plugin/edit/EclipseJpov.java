///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: EclipseJpov.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jack.plugin.edit;

import jack.util.Logger;

import java.net.MalformedURLException;
import java.net.URL;

import jpov.viewer.JpovViewer;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;

/**
 * Eclipse-specific part of jpov viewer.
 * @author A. Requet
 */
public class EclipseJpov extends JpovViewer {
	// Image descriptors corresponding to the loaded images.
	static ImageDescriptor PROVED_DESCRIPTOR;
	static ImageDescriptor UNPROVED_DESCRIPTOR;
	static ImageDescriptor PROVE_DESCRIPTOR;
	static ImageDescriptor SAVE_DESCRIPTOR;
	static ImageDescriptor ONLINE_DESCRIPTOR;
	static ImageDescriptor OFFLINE_DESCRIPTOR;
	public static ImageDescriptor FILTER_DESCRIPTOR;
	public static ImageDescriptor PRINTER_DESCRIPTOR;
	static ImageDescriptor INVARIANT_DESCRIPTOR;
	static ImageDescriptor LOCALES_DESCRIPTOR;
	static ImageDescriptor ENSURES_DESCRIPTOR;
	static ImageDescriptor EXSURES_DESCRIPTOR;
	static ImageDescriptor ASSERT_DESCRIPTOR;
	static ImageDescriptor REQUIRES_DESCRIPTOR;
	static ImageDescriptor LOOP_INVARIANT_DESCRIPTOR;
	static ImageDescriptor LOOP_EXSURES_DESCRIPTOR;
	public static ImageDescriptor REMOVE_TASK_DESCRIPTOR;
	public static ImageDescriptor REMOVE_ALL_TASKS_DESCRIPTOR;
	public static ImageDescriptor TASK_RUNNING_DESCRIPTOR;
	static ImageDescriptor TASK_WAITING_DESCRIPTOR;
	static ImageDescriptor TASK_FINISHED_DESCRIPTOR;
	static ImageDescriptor CHECKED_DESCRIPTOR;
	public static ImageDescriptor COMPILED_DESCRIPTOR;

	public static Image TASK_RUNNING;
	public static Image TASK_WAITING;
	public static Image TASK_FINISHED;

	private static ImageDescriptor imgDesc(
		URL image_location,
		String file_name)
		throws MalformedURLException {
		return ImageDescriptor.createFromURL(
			new URL(image_location, file_name));
	}

	/** 
	 * load the images PROVED, UNPROVED, PROVE and SAVE 
	 * 
	 * @param images_location an URL corresponding to the directory where the 
	 *         images are located.
	 */
	/*@ 
	  @ ensures PROVED   != null;
	  @ ensures UNPROVED != null;
	  @ ensures PROVE    != null;
	  @ ensures SAVE     != null;
	  @*/
	public static void initImages(URL images_location) {
		try {
			if (PROVED == null) {
				PROVED_DESCRIPTOR = imgDesc(images_location, "proof_ok.gif");
				PROVED = PROVED_DESCRIPTOR.createImage();

				UNPROVED_DESCRIPTOR =
					imgDesc(images_location, "error_orange.gif");
				UNPROVED = UNPROVED_DESCRIPTOR.createImage();

				PROVE_DESCRIPTOR = imgDesc(images_location, "thread_obj.gif");
				PROVE = PROVE_DESCRIPTOR.createImage();

				SAVE_DESCRIPTOR = imgDesc(images_location, "save_edit.gif");
				SAVE = SAVE_DESCRIPTOR.createImage();

				ONLINE_DESCRIPTOR = imgDesc(images_location, "online.gif");
				ONLINE = ONLINE_DESCRIPTOR.createImage();

				OFFLINE_DESCRIPTOR = imgDesc(images_location, "offline.gif");
				OFFLINE = OFFLINE_DESCRIPTOR.createImage();

				FILTER_DESCRIPTOR = imgDesc(images_location, "filter_ps.gif");
				FILTER = FILTER_DESCRIPTOR.createImage();

				PRINTER_DESCRIPTOR = imgDesc(images_location, "printer.gif");
				PRINTER = PRINTER_DESCRIPTOR.createImage();

				INVARIANT_DESCRIPTOR =
					imgDesc(images_location, "invariant.gif");
				INVARIANT = INVARIANT_DESCRIPTOR.createImage();

				ENSURES_DESCRIPTOR = imgDesc(images_location, "ensures.gif");
				ENSURES = ENSURES_DESCRIPTOR.createImage();

				EXSURES_DESCRIPTOR = imgDesc(images_location, "exsures.gif");
				EXSURES = EXSURES_DESCRIPTOR.createImage();
				
				ASSERT_DESCRIPTOR = imgDesc(images_location, "assert.gif");
				ASSERT = ASSERT_DESCRIPTOR.createImage();

				REQUIRES_DESCRIPTOR = imgDesc(images_location, "requires.gif");
				REQUIRES = REQUIRES_DESCRIPTOR.createImage();

				LOOP_INVARIANT_DESCRIPTOR =
					imgDesc(images_location, "loop_invariant.gif");
				LOOP_INVARIANT = LOOP_INVARIANT_DESCRIPTOR.createImage();

				LOOP_EXSURES_DESCRIPTOR =
					imgDesc(images_location, "loop_exsures.gif");
				LOOP_EXSURES = LOOP_EXSURES_DESCRIPTOR.createImage();

				LOCALES_DESCRIPTOR = imgDesc(images_location, "local.gif");
				LOCALES = LOCALES_DESCRIPTOR.createImage();

				REMOVE_TASK_DESCRIPTOR =
					imgDesc(images_location, "remove_task.gif");

				REMOVE_ALL_TASKS_DESCRIPTOR =
					imgDesc(images_location, "remove_all_tasks.gif");

				TASK_WAITING_DESCRIPTOR =
					imgDesc(images_location, "task_waiting.gif");
				TASK_WAITING = TASK_WAITING_DESCRIPTOR.createImage();

				TASK_RUNNING_DESCRIPTOR =
					imgDesc(images_location, "task_running.gif");
				TASK_RUNNING = TASK_RUNNING_DESCRIPTOR.createImage();

				TASK_FINISHED_DESCRIPTOR =
					imgDesc(images_location, "task_finished.gif");
				TASK_FINISHED = TASK_FINISHED_DESCRIPTOR.createImage();

				CHECKED_DESCRIPTOR =
					imgDesc(images_location, "proof_checked.gif");
				CHECKED = CHECKED_DESCRIPTOR.createImage();

				COMPILED_DESCRIPTOR = imgDesc(images_location, "compiled.gif");
//				COMPILED_DESCRIPTOR.createImage();

				provedImages = new Image[PROVED_IMAGES_COUNT];
				int image_num = 1;
				for (int i = 0; i < PROVED_IMAGES_COUNT; ++i, ++image_num) {
					ImageDescriptor img;
					img =
						imgDesc(
							images_location,
							"proved_" + image_num + ".gif");
					provedImages[i] = img.createImage();
				}
			}
		} catch (MalformedURLException e) {
			Logger.err.println("Cannot find images :" + e.toString());
		}
	}

}
