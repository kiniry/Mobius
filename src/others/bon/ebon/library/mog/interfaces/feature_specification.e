indexing
	description: "The complete specification of a single feature of a class."

class
	FEATURE_SPECIFICATION

inherit
	HASHABLE
	
feature -- Access

	hash_code: INTEGER is
			-- Hash code value
		do
				check false end
		end

feature -- Measurement

feature -- Status report

feature -- Status setting

feature -- Cursor movement

feature -- Element change

feature -- Removal

feature -- Resizing

feature -- Transformation

feature -- Conversion

feature -- Duplication

feature -- Miscellaneous

feature -- Basic operations

feature -- Obsolete

feature -- Inapplicable

feature {NONE} -- Implementation

	feature_status: ANY -- enumeration of deferred, effective, redefined
	feature_name_list: ANY -- MOG_LIST[STRING]?
	type_information: ANY
	rename_clause: ANY
	comment: COMMENT
	arguments: ANY
	contract: ANY

invariant
	invariant_clause: True -- Your invariant here

end -- class FEATURE_SPECIFICATION
