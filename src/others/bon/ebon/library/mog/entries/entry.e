indexing
   description: "A generic entry in a chart."

deferred class
   ENTRY

inherit
   BON_TEXT

feature -- Removal

	wipe_out is
		-- Remove all contents.
		deferred
		end
		
end -- class ENTRY
