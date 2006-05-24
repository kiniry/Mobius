//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ProofTaskList.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jack.plugin.prove;

import java.util.Collection;
import java.util.Iterator;
import java.util.Vector;

/**
 * List of proofs that should be performed.
 * 
 * It also defines a thread that will try to run a task each time it is 
 * awakened.
 * @author A. Requet
 */
class ProofTaskList extends Thread {

	/**
	 * Indicates that the provider should not be notified. This is used
	 * when adding several tasks at once in order to allows notifying
	 * the provider only once.
	 */
	int freezeNotify;

	/**
	 * The viewer object associated to this list.
	 */
	private ProofContentProvider provider;

	/**
	 * Boolean indicating that the thread should stop.
	 */
	private boolean shouldStop;

	/**
	 * Number of tasks that can be performed simulteanously. 
	 */
	private int maxRunning;

	/**
	 * Number of currently running tasks. This number can be more than
	 * <code>maxRunning</code> if <code>startProof</code> is called.
	 */
	private int runningTasks;

	/**
	 * Vector holding the proof tasks.
	 */
	private Collection proofTasks;

	/**
	 * Creates a new empty <code>ProofTaskList</code>.
	 */
	public ProofTaskList(int maxRunning) {
		super("ProofTask runner");
		proofTasks = new Vector();
		runningTasks = 0;
		this.maxRunning = maxRunning;
	}

	public synchronized void setProvider(ProofContentProvider provider) {
		this.provider = provider;
	}

	/**
	 * Add a proof task to the list and wake up the proof task manager.
	 * 
	 * @param t the tas k to add.
	 **/
	public synchronized void add(ProofTask t) {
		proofTasks.add(t);
		t.setProofTaskList(this);
		notifyProvider();
		notifyAll();
	}

	/**
	 * Removes the given <code>ProofTask</code> object from the 
	 * list.
	 */
	public synchronized void remove(ProofTask tsk) {
		// stops the task if it is running
		tsk.stopAsSoonAsYouCanPlease();
	}

	public synchronized void freezeNotify() {
		++freezeNotify;
	}

	public synchronized void unfreezeNotify() {
		--freezeNotify;
		notifyProvider();
	}

	/**
	 * Removes all the tasks that are in the finished state from the 
	 * list.
	 */
	public synchronized void removeFinished() {
		int removed_count = 0;

		Iterator i = proofTasks.iterator();
		while (i.hasNext()) {
			ProofTask tsk = (ProofTask) i.next();
			// removes the task if it is finished.
			if (tsk.getCurrentState() == ProofTask.FINISHED) {
				i.remove();
				++removed_count;
			}
		}

		if (runningTasks == 0) {
			notifyProvider();
		}
	}

	public synchronized void removeAll() {
		int removed_count = 0;

		Iterator i = proofTasks.iterator();
		while (i.hasNext()) {
			ProofTask tsk = (ProofTask) i.next();
			// removes the task if it is finished.
			if (tsk.getCurrentState() == ProofTask.FINISHED
				|| tsk.getCurrentState() == ProofTask.ERROR
				|| tsk.getCurrentState() == ProofTask.STOPPED
				|| tsk.getCurrentState() == ProofTask.WAITING) {
				i.remove();
				++removed_count;
			}
		}

		if (runningTasks == 0) {
			notifyProvider();
		}
	}
	/**
	 * Tries to start the given proof if possible. 
	 */
	public synchronized void startProof(ProofTask tsk) {
		tsk.start();
		++runningTasks;
	}

	public synchronized void recompile(ProofTask tsk) {
		tsk.recompile();
	}

	public synchronized void edit(ProofTask tsk) {
		tsk.edit();
	}

	public synchronized void reprove(ProofTask tsk, ProofTask pt) {
		tsk.reprove(pt);
	}

	/**
	 * Tries to stop all the proofs.
	 */
	public synchronized void stopAll() {
		Iterator i = proofTasks.iterator();

		while (i.hasNext()) {
			ProofTask tsk = (ProofTask) i.next();
			tsk.stopAsSoonAsYouCanPlease();
		}
	}

	public Object[] toArray() {
		return proofTasks.toArray();
	}

	/**
	 * Indicate the thread that it should stop as soon as it can.
	 */
	public void stopPlease() {
		shouldStop = true;
	}

	/**
	 * Called by tasks when their status changes.
	 */
	public void taskChanged(ProofTask tsk) {
		notifyProvider();
	}

	/**
	 * Notify the content provider associated to this list that the
	 * content has changed.
	 */
	public void notifyProvider() {
		if (provider != null && freezeNotify <= 0) {
			// refresh the viewer
			provider.contentChanged();
		}
	}

	/**
	 * Called by a task when it has finished.
	 * 
	 * This decrements the number of running tasks, and awake the 
	 * task starting threads.
	 */
	public synchronized void taskFinished(ProofTask tsk) {
		--runningTasks;
		tsk.unlock();
		notifyAll();
	}

	/**
	 * This thread loops until <code>stopPlease</code> is called.
	 * Each loop iteration tries to start tasks that are in the 
	 * <code>WAITING</code> state so that there are <code>maxRunning</code>
	 * tasks running.
	 * 
	 * When there are no more tasks in the <code>WAITING</code> state or 
	 * when there are <code>maxRunning</code> tasks running, this threads
	 * waits to be notified.
	 * 
	 * This thread is then awakened each time a task is added or when a task
	 * finishes.
	 */
	private synchronized void runTasks() {
		while (!shouldStop) {
			// perform one run.
			Iterator i = proofTasks.iterator();

			while (i.hasNext() && runningTasks < maxRunning) {
				ProofTask tsk = (ProofTask) i.next();

				if (tsk.getCurrentState() == ProofTask.WAITING) {
					// starts the task
					tsk.start();
					++runningTasks;
				}
			}

			// wait for a task to be added or a task to finish
			try {
				wait();
			} catch (InterruptedException e) {
			}
		}
		// stop all the children threads
		stopAll();
	}

	public void run() {
		runTasks();
	}
}
