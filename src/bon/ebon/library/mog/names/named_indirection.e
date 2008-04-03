indexing
	description: "A named indirection consisting of a class name and a %
							% parameterized indirection list."

class NAMED_INDIRECTION

inherit
	ANY

	BON_TEXT

	HASHABLE
	
creation
	make

feature -- Initialization

	make (a_class_name: STRING;
				an_indirection_list: INDIRECTION_LIST) is
			-- Initialize `Current'.
		require
			a_class_name /= Void and then not a_class_name.is_empty
			an_indirection_list /= Void and then not an_indirection_list.is_empty
		do
			my_class_name := a_class_name.twin
			my_indirection_list := an_indirection_list.twin
		ensure
			class_name.is_equal (a_class_name)
			indirection_list.is_equal (an_indirection_list)
		end
		
feature -- Access

	class_name: STRING is
			-- The class name of this named indirection.
		do
			Result := my_class_name.twin
		ensure
			Result /= Void and then not Result.is_empty
		end
	
	indirection_list: INDIRECTION_LIST is
			-- The indirection list of this named indirection.
		do
			Result := my_indirection_list.twin
		ensure
			Result /= Void and then not Result.is_empty
		end

	hash_code: INTEGER is
		do
			Result := my_class_name.hash_code
		end
		
feature -- Output

	bon_out: STRING is
		do
			Result := my_class_name.twin
			Result.append (" [")
			Result.append (my_indirection_list.bon_out)
			Result.append (" ]")
		end

feature {NAMED_INDIRECTION} -- Implementation

	my_class_name: STRING
	my_indirection_LIST: INDIRECTION_LIST

invariant

	my_class_name /= Void and then not my_class_name.is_empty
	my_indirection_list /= Void and then not my_indirection_list.is_empty

end -- class NAMED_INDIRECTION
