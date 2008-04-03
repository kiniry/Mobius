indexing
	description: "A collection of features of a class."

class
	FEATURE_CLAUSE

inherit
	HASHABLE

feature -- Access

	hash_code: INTEGER is
		do
				check false end
		end

	selective_export: SELECTIVE_EXPORT_SET is
			-- The optional export list of this collection of features.
		do
		end

	comment: COMMENT is
			-- The optional comment applied to this collection of features.
		do
		end

	feature_specifications: FEATURE_SPECIFICATION_LIST is
		do
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

	my_selective_exports: SELECTIVE_EXPORT_SET
	my_comment: COMMENT
	my_feature_specifications: FEATURE_SPECIFICATION_LIST

invariant
	invariant_clause: True -- Your invariant here

end -- class FEATURE_CLAUSE
