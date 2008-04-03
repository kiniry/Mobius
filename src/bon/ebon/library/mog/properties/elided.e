indexing
	description: "Objects that can possibly be elided for information hiding."
	author: "Joseph R. Kiniry <kiniry@kindsoftware.com>"
	date: "$Date: 2005/05/02 22:58:29 $"
	revision: "$Revision: 1.1 $"

deferred class
	ELIDED

feature -- Initialization

	make_ellipses is
		-- Initialize `Current' to represent an ellipses token (i.e., a set 
		-- of missing static components).
		do
			set_ellipses (True)
		end

feature -- Access

	ellipses: BOOLEAN is
			-- Is this static component an ellipses placeholder?
		do
			Result := my_ellipses
		end

feature -- Element change

	set_ellipses (ellipses_flag: BOOLEAN) is
			-- Set the ellipses flag of `Current'.
		do
			my_ellipses := True
		end

feature -- Output

	bon_out: STRING is
		do
			if ellipses then
				Result := "..."
			else Result := ""
			end
		ensure then
			ellipses implies Result.is_equal ("...") or else Result.is_equal ("")
		end

feature {STATIC_COMPONENT} -- Implementation

	my_ellipses: BOOLEAN

end -- class ELIDED
