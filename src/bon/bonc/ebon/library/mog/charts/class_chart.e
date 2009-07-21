indexing
	description: "A class chart."

class
	CLASS_CHART

inherit
	INFORMAL_CHART
		redefine
			bon_out,
			canonicalize,
			copy, is_equal,
			is_part_of, contains, is_disjoint,
			merge, intersect, subtract, symdif,
			wipe_out
		end

creation
	make

feature -- Initialization

	make (a_name: STRING;
				an_index: INDEX_LIST;
				an_explanation: STRING;
				a_part: STRING;
				some_parents: CLASS_NAME_LIST;
				some_queries: QUERY_LIST;
				some_commands: COMMAND_LIST;
				some_constraints: CONSTRAINT_LIST) is
			-- Initialize `Current'.
		require
			a_name /= Void
			an_explanation /= Void
			a_part /= Void
		do
			make_informal_chart (a_name, an_index, an_explanation, a_part)
			my_parents := some_parents.twin
			my_queries := some_queries.twin
			my_commands := some_commands.twin
			my_constraints := some_constraints.twin
		ensure
			name.is_equal (a_name)
			index.is_equal (an_index)
			explanation.is_equal (an_explanation)
			part.is_equal (a_part)
			parents_initialized: parents.is_equal (some_parents)
			queries_initialized: queries.is_equal (some_queries)
			commands_initialized: commands.is_equal (some_commands)
			constraints_initialized: constraints.is_equal (some_constraints)
		end

feature -- Duplication

	copy (other: like Current) is
		do
			Precursor (other)
			set_parents (other.parents)
			set_queries (other.queries)
			set_commands (other.commands)
			set_constraints (other.constraints)
		end

feature -- Access

	parents: CLASS_NAME_LIST is
		do
			Result := my_parents.twin
		ensure
			non_void_result: Result /= Void
		end

	queries: QUERY_LIST is
		do
			Result := my_queries.twin
		ensure
			non_void_result: Result /= Void
		end

	commands: COMMAND_LIST is
		do
			Result := my_commands.twin
		ensure
			non_void_result: Result /= Void
		end

	constraints: CONSTRAINT_LIST is
		do
			Result := my_constraints.twin
		ensure
			non_void_result: Result /= Void
		end

feature -- Measurement

	parents_count: INTEGER is
		do
			Result := my_parents.count
		ensure
			non_negative_result: Result >= 0
		end

	queries_count: INTEGER is
		do
			Result := my_queries.count
		ensure
			non_negative_result: Result >= 0
		end

	commands_count: INTEGER is
		do
			Result := my_commands.count
		ensure
			non_negative_result: Result >= 0
		end

	constraints_count: INTEGER is
		do
			Result := my_constraints.count
		ensure
			non_negative_result: Result >= 0
		end

feature -- Status report

	is_part_of (other: like Current): BOOLEAN is
		do
			Result := Precursor (other) and
				my_parents.is_part_of (other.my_parents) and
				my_queries.is_part_of (other.my_queries) and
				my_commands.is_part_of (other.my_commands) and
				my_constraints.is_part_of (other.my_constraints)
		end

	contains (other: like Current): BOOLEAN is
		do
			Result := Precursor (other) and
				my_parents.contains (other.my_parents) and
				my_queries.contains (other.my_queries) and
				my_commands.contains (other.my_commands) and
				my_constraints.contains (other.my_constraints)
		end

	is_disjoint (other: like Current): BOOLEAN is
		do
			Result := Precursor (other) and
				my_parents.is_disjoint (other.my_parents) and
				my_queries.is_disjoint (other.my_queries) and
				my_commands.is_disjoint (other.my_commands) and
				my_constraints.is_disjoint (other.my_constraints)
		end

feature -- Comparison

	is_equal (other: like Current): BOOLEAN is
		do
			Result := Precursor (other) and 
				my_parents.is_equal (other.my_parents) and
				my_queries.is_equal (other.my_queries) and
				my_commands.is_equal (other.my_commands) and
				my_constraints.is_equal (other.my_constraints)
			ensure then
				Result implies parents.count = other.parents.count and
					queries.count = other.queries.count and
					commands.count = other.commands.count and
					constraints.count = other.constraints.count
		end

feature -- Element change

	-- parents

	set_parents (some_parents: CLASS_NAME_LIST) is
		do
			my_parents := some_parents.twin
		ensure
			parents.is_equal (some_parents)
		end

	add_parents (some_parents: CLASS_NAME_LIST) is
		do
			my_parents := my_parents.merge (some_parents.twin)
		ensure
			some_parents.is_part_of (parents)
			parents_count = my_parents.merge (some_parents).count
		end

	add_parent (a_parent: STRING) is
		require
			a_parent /= Void implies not a_parent.is_empty
		do
			my_parents.put_last (a_parent.twin)
		ensure
			parents.has (a_parent)
			not (old parents).has (a_parent) implies parents_count = old parents_count + 1
			(old parents).has (a_parent) implies parents_count = old parents_count
		end

	-- queries

	set_queries (some_queries: QUERY_LIST) is
		do
			my_queries := some_queries.twin
		ensure
			queries.is_equal (some_queries)
		end

	add_queries (some_queries: QUERY_LIST) is
		do
			my_queries := my_queries.merge (some_queries.twin)
		ensure
			some_queries.is_part_of (queries)
			queries_count = queries.merge (some_queries).count
		end

	add_query (a_query: STRING) is
		require
			a_query /= Void implies not a_query.is_empty
		do
			my_queries.put_last (a_query.twin)
		ensure
			queries.has (a_query)
			not (old queries).has (a_query) implies queries_count = old queries_count + 1
			(old queries).has (a_query) implies queries_count = old queries_count
		end

	-- commands

	set_commands (some_commands: COMMAND_LIST) is
		do
			my_commands :=  some_commands.twin
		ensure
			commands.is_equal (some_commands)
		end

	add_commands (some_commands: COMMAND_LIST) is
		do
			my_commands := my_commands.merge (some_commands.twin)
		ensure
			some_commands.is_part_of (commands)
			commands_count = commands.merge (some_commands).count
		end

	add_command (a_command: STRING) is
		require
			a_command /= Void implies not a_command.is_empty
		do
			my_commands.put_last (a_command.twin)
		ensure
			commands.has (a_command)
			not (old commands).has (a_command) implies commands_count = old commands_count + 1
			(old commands).has (a_command) implies commands_count = old commands_count
		end

	-- constraints

	set_constraints (some_constraints: CONSTRAINT_LIST) is
		do
			my_constraints := some_constraints.twin
		ensure
			constraints.is_equal (some_constraints)
		end

	add_constraints (some_constraints: CONSTRAINT_LIST) is
		do
			my_constraints := my_constraints.merge (some_constraints.twin)
		ensure
			some_constraints.is_part_of (constraints)
			constraints_count = constraints.merge (some_constraints).count
		end

	add_constraint (a_constraint: STRING) is
		require
			a_constraint /= Void implies not a_constraint.is_empty
		do
			my_constraints.put_last (a_constraint.twin)
		ensure
			constraints.has (a_constraint)
			not (old constraints).has (a_constraint) implies constraints_count = old constraints_count + 1
			(old constraints).has (a_constraint) implies constraints_count = old constraints_count
		end

feature -- Removal

	wipe_out is
			-- Remove all contents.
		do
			Precursor
			clear_parents
			clear_queries
			clear_commands
			clear_constraints
		ensure then
			parents.is_empty
			queries.is_empty
			commands.is_empty
			constraints.is_empty
		end

	-- parents

	clear_parents is
		do
			my_parents.wipe_out
		ensure
			parents.is_empty
		end

	remove_parents (some_parents: CLASS_NAME_LIST) is
		do
			my_parents := my_parents.subtract (some_parents)
		ensure
			parents.is_disjoint (some_parents)
			parents_count = old parents_count - parents.intersect (some_parents).count
		end

	remove_parent (a_parent: STRING) is
		do
			my_parents.delete (a_parent)
		ensure
			not parents.has (a_parent)
			old parents.has (a_parent) implies parents_count = old parents_count - 1
			not old parents.has (a_parent) implies parents_count = old parents_count
		end

	-- queries

	clear_queries is
		do
			my_queries.wipe_out
		ensure
			queries.is_empty
		end

	remove_queries (some_queries: QUERY_LIST) is
		do
			my_queries := my_queries.subtract (some_queries)
		ensure
			queries.is_disjoint (some_queries)
			queries_count = old queries_count - queries.intersect (some_queries).count
		end

	remove_query (a_query: STRING) is
		do
			my_queries.delete (a_query)
		ensure
			not queries.has (a_query)
			old queries.has (a_query) implies queries_count = old queries_count - 1
			not old queries.has (a_query) implies queries_count = old queries_count
		end

	-- commands

	clear_commands is
		do
			my_commands.wipe_out
		ensure
			commands.is_empty
		end

	remove_commands (some_commands: COMMAND_LIST) is
		do
			my_commands := my_commands.subtract (some_commands)
		ensure
			commands.is_disjoint (some_commands)
			commands_count = old commands_count - commands.intersect (some_commands).count
		end

	remove_command (a_command: STRING) is
		do
			my_commands.delete (a_command)
		ensure
			not commands.has (a_command)
			old commands.has (a_command) implies commands_count = old commands_count - 1
			not old commands.has (a_command) implies commands_count = old commands_count
		end

	-- constraints

	clear_constraints is
		do
			my_constraints.wipe_out
		ensure
			constraints.is_empty
		end

	remove_constraints (some_constraints: CONSTRAINT_LIST) is
		do
			my_constraints := my_constraints.subtract (some_constraints)
		ensure
			constraints.is_disjoint (some_constraints)
			constraints_count = old constraints_count - constraints.intersect (some_constraints).count
		end

	remove_constraint (a_constraint: STRING) is
		do
			my_constraints.delete (a_constraint)
		ensure
			not constraints.has (a_constraint)
			old constraints.has (a_constraint) implies constraints_count = old constraints_count - 1
			not old constraints.has (a_constraint) implies constraints_count = old constraints_count
		end

feature -- Transformation

	canonicalize: like Current is
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor
			create Result.make (informal_chart.name, informal_chart.index, 
				informal_chart.explanation, informal_chart.part,
				Void, Void, Void, Void)
			Result.set_parents (parents.canonicalize)
			Result.set_queries (queries.canonicalize)
			Result.set_commands (commands.canonicalize)
			Result.set_constraints (constraints.canonicalize)
		end

feature -- Output

	bon_out: STRING is
		do
			Result := "class_chart " + my_name.out + "%N"
			Result.append (Precursor)
			if my_parents.count /= 0 then
				Result.append ("inherit " + my_parents.bon_out + "%N")
			end
			Result.append ("query%N" + my_queries.bon_out)
			Result.append ("command%N" + my_commands.bon_out)
			Result.append ("constraint%N" + my_constraints.bon_out)
			Result.append ("end%N")
		end

feature -- Basic operations

	merge (other: like Current): like Current is
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor (other)
			create Result.make (informal_chart.name, informal_chart.index, 
				informal_chart.explanation, informal_chart.part,
				Void, Void, Void, Void)
			Result.set_parents (parents.merge (other.parents))
			Result.set_queries (queries.merge (other.queries))
			Result.set_commands (commands.merge (other.commands))
			Result.set_constraints (constraints.merge (other.constraints))
		end

	intersect (other: like Current): like Current is
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor (other)
			create Result.make (informal_chart.name, informal_chart.index, 
				informal_chart.explanation, informal_chart.part,
				Void, Void, Void, Void)
			Result.set_parents (parents.intersect (other.parents))
			Result.set_queries (queries.intersect (other.queries))
			Result.set_commands (commands.intersect (other.commands))
			Result.set_constraints (constraints.intersect (other.constraints))
		end

	subtract (other: like Current): like Current is
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor (other)
			create Result.make (informal_chart.name, informal_chart.index, 
				informal_chart.explanation, informal_chart.part,
				Void, Void, Void, Void)
			Result.set_parents (parents.subtract (other.parents))
			Result.set_queries (queries.subtract (other.queries))
			Result.set_commands (commands.subtract (other.commands))
			Result.set_constraints (constraints.subtract (other.constraints))
		end

	symdif (other: like Current): like Current is
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor (other)
			create Result.make (informal_chart.name, informal_chart.index, 
				informal_chart.explanation, informal_chart.part,
				Void, Void, Void, Void)
			Result.set_parents (parents.symdif (other.parents))
			Result.set_queries (queries.symdif (other.queries))
			Result.set_commands (commands.symdif (other.commands))
			Result.set_constraints (constraints.symdif (other.constraints))
		end

feature {CLASS_CHART} -- Implementation

	my_parents: CLASS_NAME_LIST
	my_queries: QUERY_LIST
	my_commands: COMMAND_LIST
	my_constraints: CONSTRAINT_LIST

invariant
	
	parents /= Void
	queries /= Void
	commands /= Void
	constraints /= Void

end
