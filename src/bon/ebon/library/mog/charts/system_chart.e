indexing
	description: "A system chart."

class
	SYSTEM_CHART

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
				some_clusters: CLUSTER_ENTRIES) is
			-- Initialize `Current'.
		require
			a_name /= Void
			an_explanation /= Void
			a_part /= Void
		do
			make_informal_chart (a_name, an_index, an_explanation, a_part)
			create my_clusters.make_from_set (some_clusters)
		ensure
			name.is_equal (a_name)
			index.is_equal (an_index)
			explanation.is_equal (an_explanation)
			part.is_equal (a_part)
			clusters.is_equal (some_clusters)
		end

feature -- Duplication

	copy (other: like Current) is
		do
			Precursor (other)
			set_clusters (other.clusters)
		end

feature -- Access

	clusters: CLUSTER_ENTRIES is
		do
			Result := my_clusters.twin
		ensure
			non_void_result: Result /= Void
		end

feature -- Measurement

	clusters_count: INTEGER is
		do
			Result := my_clusters.count
		ensure
			non_negative_result: Result >= 0
		end

feature -- Status report

	is_part_of (other: like Current): BOOLEAN is
		do
			Result := Precursor (other) and
				clusters.is_part_of (other.clusters)
		end

	contains (other: like Current): BOOLEAN is
		do
			Result := Precursor (other) and
				clusters.contains (other.clusters)
		end

	is_disjoint (other: like Current): BOOLEAN is
		do
			Result := Precursor (other) and
				clusters.is_disjoint (other.clusters)
		end

feature -- Comparison

	is_equal (other: like Current): BOOLEAN is
		do
			Result := Precursor (other) and 
				 clusters.is_equal (other.clusters)
		ensure then
			clusters.is_equal (other.clusters)
		end

feature -- Element change

	set_clusters (some_clusters: CLUSTER_ENTRIES) is
		do
			my_clusters := clusters.twin
		ensure
			clusters.is_equal (some_clusters)
		end

	add_clusters (some_clusters: CLUSTER_ENTRIES) is
		do
			my_clusters := my_clusters.merge (some_clusters.twin)
		ensure
			some_clusters.is_part_of (clusters)
			clusters_count = clusters.merge (some_clusters).count
		end

	add_cluster (a_cluster: CLUSTER_ENTRY) is
		require
			a_cluster /= Void
		do
			my_clusters.put (a_cluster)
		ensure
			clusters.has (a_cluster)
			not (old clusters).has (a_cluster) implies clusters_count = old clusters_count + 1
		end

feature -- Removal

	wipe_out is
			-- Remove all contents.
		do
			Precursor
			clear_clusters
		ensure then
			clusters.is_empty
		end

	clear_clusters is
		do
			my_clusters.wipe_out
		ensure
			clusters.is_empty
		end

	remove_clusters (some_clusters: CLUSTER_ENTRIES) is
		do
			my_clusters := my_clusters.subtract (some_clusters)
		ensure
			clusters.is_disjoint (some_clusters)
			clusters_count = old clusters_count - clusters.intersect (some_clusters).count
		end

	remove_cluster (a_cluster: CLUSTER_ENTRY) is
		do
			my_clusters.remove (a_cluster)
		ensure
			not clusters.has (a_cluster)
			old clusters.has (a_cluster) implies clusters_count = old clusters_count - 1
			not old clusters.has (a_cluster) implies clusters_count = old clusters_count
		end

feature -- Transformation

	canonicalize: like Current is
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor
			create Result.make (informal_chart.name, informal_chart.index, 
				informal_chart.explanation, informal_chart.part, Void)
			Result.set_clusters (clusters.canonicalize)
		end

feature -- Output

	bon_out: STRING is
		do
			create Result.make_from_string ("system_chart " + my_name + "%N")
			Result.append (Precursor)
			Result.append (my_clusters.bon_out)
			Result.append ("end%N")
		end

feature -- Basic operations

	merge (other: like Current): like Current is
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor (other)
			create Result.make (informal_chart.name, informal_chart.index, 
				informal_chart.explanation, informal_chart.part, Void)
			Result.set_clusters (clusters.merge (other.clusters))
		end

	intersect (other: like Current): like Current is
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor (other)
			create Result.make (informal_chart.name, informal_chart.index, 
				informal_chart.explanation, informal_chart.part, Void)
			Result.set_clusters (clusters.intersect (other.clusters))
		end

	subtract (other: like Current): like Current is
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor (other)
			create Result.make (informal_chart.name, informal_chart.index, 
				informal_chart.explanation, informal_chart.part, Void)
			Result.set_clusters (clusters.subtract (other.clusters))
		end

	symdif (other: like Current): like Current is
		local
			informal_chart: INFORMAL_CHART
		do
			informal_chart := Precursor (other)
			create Result.make (informal_chart.name, informal_chart.index, 
				informal_chart.explanation, informal_chart.part, Void)
			Result.set_clusters (clusters.symdif (other.clusters))
		end

feature {SYSTEM_CHART} -- Implementation

	my_clusters: CLUSTER_ENTRIES

invariant

	clusters /= Void

end -- class SYSTEM_CHART
