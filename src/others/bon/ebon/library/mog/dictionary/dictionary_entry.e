indexing
	description: "An entry in a class dictionary."

class
	DICTIONARY_ENTRY

inherit
	ENTRY

	HASHABLE

creation
	make

feature -- Initialization

	make (a_class: STRING; 
			a_cluster: STRING; 
			a_description: STRING) is
			-- Initialize `Current'.
		do
			create my_class.make_from_string (a_class)
			create my_cluster.make_from_string (a_cluster)
			create my_description.make_from_string (a_description)
		ensure
			class_name = a_class
			cluster = a_cluster
			description = a_description
		end

feature -- Access

	hash_code: INTEGER is
		local
			string_to_hash: STRING
		do
			create string_to_hash.make_from_string (my_class)
			string_to_hash.append (my_cluster)
			string_to_hash.append (my_description)

			Result := string_to_hash.hash_code
		end

	class_name: STRING is
			-- The class of `Current'.
		do
			Result := my_class.twin
		end

	cluster: STRING is
			-- The cluster of `Current'.
		do
			Result := my_cluster.twin
		end

	description: STRING is
			-- The description of `Current'.
		do
			Result := my_description.twin
		end

feature -- Element change

	set_class (a_class: STRING) is
			-- Set a new class for `Current'.
		do
			my_class.wipe_out
			my_class.append (a_class.twin)
		ensure
			class_name = a_class
		end

	set_cluster (a_cluster: STRING) is
			-- Set a new cluster for `Current'.
		do
			my_cluster.wipe_out
			my_cluster.append (a_cluster.twin)
		ensure
			cluster = a_cluster
		end

	set_description (a_description: STRING) is
			-- Set a description for `Current'.
		do
			my_description.wipe_out
			my_description.append (a_description.twin)
		ensure
			description = a_description
		end

feature -- Removal

	wipe_out is
		do
			clear_class
			clear_cluster
			clear_description
		ensure then
			my_class.is_empty
			my_cluster.is_empty
			my_description.is_empty
		end

	clear_class is
			-- Clear class of `Current'.
		do
			my_class.wipe_out
		ensure
			class_name.is_empty
		end

	clear_cluster is
			-- Clear cluster of `Current'.
		do
			cluster.wipe_out
		ensure
			cluster.is_empty
		end

	clear_description is
			-- Clear description of `Current'.
		do
			description.wipe_out
		ensure
			description.is_empty
		end

feature -- Transformation

	canonicalize is
		do
			check false end
		end

feature -- Output

	bon_out: STRING is
		do
			create Result.make_from_string ("class " + my_class.out)
			Result.append (" cluster " + my_cluster.out + "%N")
			Result.append ("description%N")
			Result.append ("%"" + my_description.out + "%"%N")
		end

feature {DICTIONARY_ENTRY} -- Implementation

	my_class: STRING
	my_cluster: STRING
	my_description: STRING

invariant

	my_class /= Void
	my_cluster /= Void
	my_description /= Void

end -- class DICTIONARY_ENTRY
