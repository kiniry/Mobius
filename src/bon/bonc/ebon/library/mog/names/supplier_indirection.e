indexing
	description: "Objects that..."
	author: "Joseph R. Kiniry <kiniry@kindsoftware.com>"
	date: "$Date: 2005/12/21 14:06:18 $"
	revision: "$Revision: 1.2 $"

class SUPPLIER_INDIRECTION

creation
	make

feature -- Initialization

  make (an_optional_indirection_feature_part: FEATURE_NAME_LIST;
		  a_generic_indirection: GENERIC_INDIRECTION) is
		-- Initialize `Current' with the given information.
		require
			an_optional_indirection_feature_part /= Void implies
				not an_optional_indirection_feature_part.is_empty
			a_generic_indirection /= Void
		do
			my_indirection_feature_part := an_optional_indirection_feature_part.twin
			my_generic_indirection := a_generic_indirection.twin
		ensure
			an_optional_indirection_feature_part /= Void implies
				indirection_feature_part.is_equal (an_optional_indirection_feature_part)
			generic_indirection.is_equal (a_generic_indirection)
		end

feature -- Access

	indirection_feature_part: FEATURE_NAME_LIST is
		do
			Result := my_indirection_feature_part.twin
		ensure
			Result /= Void implies not Result.is_empty
		end

	generic_indirection: GENERIC_INDIRECTION is
		do
			Result := my_generic_indirection.twin
		ensure
			Result /= Void
		end
	
feature {SUPPLIER_INDIRECTION} -- Implementation

	my_indirection_feature_part: FEATURE_NAME_LIST
	my_generic_indirection: GENERIC_INDIRECTION

invariant

	my_indirection_feature_part /= Void implies not my_indirection_feature_part.is_empty
	my_generic_indirection /= Void

end -- class SUPPLIER_INDIRECTION
