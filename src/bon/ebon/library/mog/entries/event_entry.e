indexing
	description: "The specification of an event and the classes involved."

class
	EVENT_ENTRY

inherit
	ENTRY

	HASHABLE
		redefine
			is_equal
		end

creation
	make

feature -- Initialization

	make (a_name: STRING; some_classes_involved: CLASS_NAME_LIST) is
			-- Initialize `Current'.
		do
			create my_name.make_from_string (a_name)
			set_classes_involved (some_classes_involved)
		ensure
			name.is_equal (a_name)
			classes_involved.to_list.contains (some_classes_involved)
		end

feature -- Access

	hash_code: INTEGER is
		do
			Result := my_name.hash_code
		end

	name: STRING is
		do
			Result := my_name.twin
		end
	
	classes_involved: CLASS_NAME_SET is
		do
			Result := my_classes_involved.twin
		end

feature -- Comparison

	is_equal (other: like Current): BOOLEAN is
		do
			Result := equal (my_name, other.my_name) and
				equal (my_classes_involved, other.my_classes_involved)
		end

feature -- Element change

	set_name (a_name: STRING) is
		require
			a_name /= Void
		do
			my_name := a_name.twin
		ensure
			name.is_equal (a_name)
		end

	set_classes_involved (some_classes_involved: CLASS_NAME_LIST) is
		require
			some_classes_involved /= Void
		do
			-- my_classes_involved := some_classes_involved.to_set
		ensure
			classes_involved.to_list.contains (some_classes_involved)
		end

feature -- Removal

	wipe_out is
		do
			clear_name
			clear_classes_involved
		ensure then
			name.is_empty
			classes_involved.is_empty
		end

	clear_name is
		do
			my_name.wipe_out
		ensure
			name.is_empty
		end

	clear_classes_involved is
		do
			my_classes_involved.wipe_out
		ensure
			classes_involved.is_empty
		end

feature -- Output

	bon_out: STRING is
		do
			create Result.make_from_string ("event%N")
			Result.append (my_name.out + "%N")
			Result.append ("involves%N")
			Result.append (my_classes_involved.bon_out)
			Result.append ("%N")
		end

feature {EVENT_ENTRY} -- Implementation

	my_name: STRING
	my_classes_involved: CLASS_NAME_SET

invariant

	my_name /= Void
	my_classes_involved /= Void

end -- class EVENT_ENTRY
