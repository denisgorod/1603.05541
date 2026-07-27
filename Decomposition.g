##### Compile the file Gamma2.g, not this one #####

####### Some variables ##########

################################### General functions #####################################

##################################### Isomorphism #######################################

#Read("simpcomp");

make_isomorphism:=function(L,isom)

	local i,j,morph, new_L;
	new_L:=ShallowCopy(L);
	
	for i in [1 .. Length(L)] do
		for j in [1 .. Length(L[1])] do
			for morph in isom do
				if morph[1] = L[i][j] then
					new_L[i][j]:=morph[2];
				fi;
			od;
		od;
		new_L[i]:=Set(new_L[i]);
	od;
	
	return new_L;
		
end;

relabeling:=function(eta)		
	
	local i, j, isom, sc_eta, new_eta, new_sc_eta, bool;
	sc_eta:=[];
	new_eta:=[];
	new_sc_eta:=[];
	
	bool:=ListWithIdenticalEntries(Length(eta),false);
	
	for i in [1..Length(eta)] do
		sc_eta[i]:=[];
		for j in [1..2] do
			sc_eta[i][j]:=SC(eta[i][j]);
		od;
	od;
	
	new_eta[1]:=eta[1];
	new_sc_eta[1]:=sc_eta[1];
	
	for i in [2..Length(eta)] do	
		for j in [1..Length(eta)] do
			isom:=SCIsomorphismEx(new_sc_eta[i-1][2],sc_eta[j][1]);
			Print(isom);
			Print("\n");
			if bool[j]=false and isom<>false and isom<>fail then
				new_eta[i]:=[make_isomorphism(eta[j][1],isom),make_isomorphism(eta[j][2],isom)];
				new_sc_eta[i]:=[SC(new_eta[i][1]),SC(new_eta[i][2])];
				bool[j]:=true;
			fi;
		od;
	od;

	return new_eta;

end;

correction:=function(eta)

	local i, new_eta, isom, new_bisfaces;
	new_bisfaces:=[];

	# BISTELLAR for the last 
	
	PrintTo("BISTELLAR.testobject","facets:=");
	PrintTo("BISTELLAR.testobject",eta[1][1]);
	PrintTo("BISTELLAR.testobject",";;");
	
	Read("BISTELLAR.g");
	
	isom:=SCIsomorphismEx(SC(eta[1][1]),SC(eta[Length(eta)][2]));
	
	new_eta:=ShallowCopy(eta);
	
	for i in [1..Length(bisfaces)-1] do
		Add(new_eta, [bisfaces[i],bisfaces[i+1]]);
	od;
	
	for i in [1..Length(bisfaces)] do
		new_bisfaces[i]:=make_isomorphism(bisfaces[i],isom);
		Add(new_eta, [new_bisfaces[i],new_bisfaces[i+1]]);
	od;

	return new_eta;
end;

############# Some general functions ######################

InsertList:=function(list1, list2, position)

	local i,temp;
	temp:=[];
	
	if position>Length(list1)+1 then
		return fail;
	fi;
	
	CopyListEntries(list1,1,1,temp,1,1,position-1);
	CopyListEntries(list2,1,1,temp,position,1,Length(list2));
	CopyListEntries(list1,position,1,temp,position+Length(list2),1,Length(list1)-position+1);
	
	for i in [1..Length(temp)] do
		list1[i]:=temp[i];
	od;
	
end;

InsertElement:=function(list, element, position)

	local temp,i;
	temp:=[];
	
	if position>Length(list)+1 then
		return fail;
	fi;
	
	for i in [0..Length(list)-position+1] do
		list[Length(list)-i+1]:=list[Length(list)-i];
	od;
	
	list[position]:=element;
	
#	CopyListEntries(list,1,1,temp,1,1,position-1);
#	Add(temp,element);
#	CopyListEntries(list,position,1,temp,position+1,1,Length(list)-position+1);
	
#	list:=ShallowCopy(temp);
	
end;

##

reverse_list:=function(list)

	local new_list, i;
	new_list:=[];
	
	for i in [1..Length(list)] do
		new_list[i]:=list[Length(list)+1-i];
	od;
		
	return new_list;

end;

##

link:=function(mfd,simplex)

	local facetsmut, facet, rest;

	facetsmut:=[];

	for facet in mfd do
		if IsSubsetSet(facet, simplex) then
			rest:=Difference(facet, simplex);
			if Length(rest) > 0 then
				Add(facetsmut, rest);
			fi;
		fi;
	od;

	return Set(facetsmut);

end;


##
# A bistellar 1-move on the edge ed is defined in the 2-sphere K exactly when ed
# has two vertices in its link and the edge that the flip would create is not
# already present.

flip_defined:=function(K, ed)

	local lk;

	if not ed in ve_count(K)[2] then
		return false;
	fi;

	lk:=Set(Flat(link(K, ed)));

	return Length(lk) = 2 and not lk in ve_count(K)[2];

end;

##
# K with the edge ed flipped: the two triangles on ed are replaced by the two
# triangles on the edge joining its link.

flip_edge:=function(K, ed)

	local lk, M;

	lk:=Set(Flat(link(K, ed)));
	M:=StructuralCopy(K);

	RemoveSet(M, Set([ed[1],ed[2],lk[1]]));
	RemoveSet(M, Set([ed[1],ed[2],lk[2]]));
	AddSet(M, Set([lk[1],lk[2],ed[1]]));
	AddSet(M, Set([lk[1],lk[2],ed[2]]));

	return M;

end;

##
ori_sub:=function(sigma,tau)

	if SignPerm(Sortex(sigma))=SignPerm(Sortex(tau)) then
		return 1;
	fi;

	return -1;

end;


##
faces_count:=function(L)

	local faces, k, element;

	faces:=[];

	for k in [1..Length(L[1])] do

	       	faces[k]:=[];
	        for element in L do
			if Length(element) >= k then
		      		UniteSet(faces[k],Combinations(element,k));
		   	fi;
	       	od;
	od;

	return faces;

end;

##
ve_count:=function(L)
	
	local locfaces, k, element;
	locfaces:=[];

	for k in [1..2] do

	        locfaces[k]:=[];
		for element in L do
			if Length(element) >= k then
		        	UniteSet(locfaces[k],Combinations(element,k));
		   	fi;
	        od;
	od;
	
	return locfaces;
end;


##
U:=function(bis)
	local result, changed, candidates, v;

	changed:=Concatenation(
		Difference(bis[1], bis[2]),
		Difference(bis[2], bis[1])
	);
	if Length(changed) = 0 then return []; fi;

	candidates:=Set(Flat(changed));
	result:=[];

	for v in candidates do
		if link(bis[1],[v])<>link(bis[2],[v]) then
			Add(result, v);
		fi;
	od;

	return Set(result);
end;

print_U_eta:=function(eta)

	local b;
	for b in [1 .. Length(eta)-1] do
		Print(b," ",U([eta[b],eta[b+1]]),"\n");
	od;

end;

##################################### Orientation ####################################################

##
induce_ori_on_link:=function(L, simplex, ori_L)

	local temp, temp_link;
	
	temp_link:=link(L, simplex)[1];
	InsertList(temp_link,simplex,1);
	#Append(temp_link,simplex);
	
	temp:=SignPerm(Sortex(temp_link));
	
	return temp * ori_L[Position(L,temp_link)];
	
end;

##
ori_check:=function(bis, ori1)

	local ori2n, j, vertex, vertemp, newface, U_bis;

	for j in [1..Length(bis[2])] do
		if bis[1][ori1[1]]=bis[2][j] then
			return [j,ori1[2]];
		fi;
	od;

	U_bis:=U(bis);

	for vertex in bis[1][ori1[1]] do
		if vertex in U_bis then
			for vertemp in Set(Flat(bis[1])) do
				newface:=ShallowCopy(bis[1][ori1[1]]);
				RemoveSet(newface,vertex);
				AddSet(newface,vertemp);
				if newface in bis[2] and not IsSubset(U_bis, newface) then
					ori2n:=((( Position( bis[1][ori1[1]], Difference(bis[1][ori1[1]], newface)[1]) - Position(newface , Difference(newface,bis[1][ori1[1]])[1]) ) mod 2) * 2) - 1;
					return [Position(bis[2], newface), ori2n * ori1[2]];
				fi;
			od;
		fi;
	od;

end;


##
ori_step:=function(L, pos, ori, bool, graph)

	local dir, num, edge, vertex_pos, vertex_num, temp, new_ori;
	
	for dir in graph do
		if pos in dir then
			if dir[1]=pos then 
				num:=dir[2];
			else 
				num:=dir[1];
			fi;
			
			if not bool[num] then
				
				#Print("Inside ori_step\n");
			
				edge:=IntersectionSet(L[num],L[pos]);
				vertex_pos:=Difference(L[pos], edge);
				vertex_num:=Difference(L[num], edge);
			
				temp:= Concatenation([vertex_pos[1]], edge);
				new_ori:= - ori[pos] * SignPerm(SortingPerm(temp));
				temp:= Concatenation([vertex_num[1]], edge);
				new_ori:= new_ori * SignPerm(SortingPerm(temp));
			
				bool[num]:=true;
				ori[num]:=new_ori;
			
			fi;
		fi;
	od;

end;

##
ori_spread:=function(L, ori)

	local i, j, adj, bool, temp_ori, beg_pos, queue, pos, num,
	      edge, vertex_pos, vertex_num, temp, new_ori;

	# Build dual graph: facets adjacent iff they share a codim-1 face
	adj:=List([1..Length(L)], x -> []);
	for i in [1..Length(L)] do
		for j in [i+1..Length(L)] do
			if Length(IntersectionSet(L[i], L[j])) = Length(L[1]) - 1 then
				Add(adj[i], j);
				Add(adj[j], i);
			fi;
		od;
	od;

	beg_pos:=ori[1];
	temp_ori:=[];
	temp_ori[beg_pos]:=ori[2];
	bool:=ListWithIdenticalEntries(Length(L),false);
	bool[beg_pos]:=true;

	# BFS propagation
	queue:=[beg_pos];
	while Length(queue) > 0 do
		pos:=Remove(queue, 1);
		for num in adj[pos] do
			if not bool[num] then
				edge:=IntersectionSet(L[num], L[pos]);
				vertex_pos:=Difference(L[pos], edge);
				vertex_num:=Difference(L[num], edge);

				temp:=Concatenation([vertex_pos[1]], edge);
				new_ori:=-temp_ori[pos] * SignPerm(SortingPerm(temp));
				temp:=Concatenation([vertex_num[1]], edge);
				new_ori:=new_ori * SignPerm(SortingPerm(temp));

				temp_ori[num]:=new_ori;
				bool[num]:=true;
				Add(queue, num);
			fi;
		od;
	od;

	return temp_ori;

end;

##
compute_ori:=function(etaa)

	local temp_ori, i, j, bool, bis, new_etaa;
	bool:=[];
	temp_ori:=[];
	new_etaa:=[];
	
	bool:=ListWithIdenticalEntries(Length(etaa),true);
	
	bis:=etaa[1];
	temp_ori[1]:=[[1,1],ori_check(bis,[1,1])];		# orientation [+/-, position]
	Add(new_etaa[1], bis);
	
	for i in [2..Length(etaa)] do
		for j in [1..Length(etaa)] do
			if etaa[j][1] = new_etaa[i-1][2] and bool[j] then
				new_etaa[i]:=etaa[j];
				bool[j]:=false;
				temp_ori[i]:=[temp_ori[i-1][2],ori_check(etaa[j],temp_ori[i-1][2])];
			fi;
		od;
	od;
	
	return [new_etaa, temp_ori];
	
end;

##
degree:=function(L)

	# Vertex degree in the 1-skeleton.
	# Valid for closed 2-manifold triangulations: in a closed surface every
	# edge belongs to exactly two triangles, so degree(v) equals the number
	# of triangles containing v.  All triangulations that appear in eta are
	# PL 2-spheres, so this holds throughout.

	local degr, facet, v;

	degr:=ListWithIdenticalEntries(Maximum(Flat(L)),0);

	for facet in L do
		for v in facet do
			degr[v]:=degr[v]+1;
		od;
	od;

	return degr;

end;

##
simp_ori:=function(L, ori, simplex)

	local element, ori_simp;
	
	ori_simp:=Set(simplex);
	for element in L do
		if element=ori_simp then
			return ori[Position(L,element)]*SignPerm(Sortex(simplex));
		fi;
	od;

end;

##
is_well_oriented:=function(eta,ori_eta)

	local i,temp_ori,temp_spread;
	temp_ori:=[];
	temp_spread:=[];
	
	temp_ori[1]:=StructuralCopy(ori_eta[1]);
	for i in [2..Length(eta)] do
		temp_ori[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
		temp_spread:=ori_spread(eta[i],temp_ori[i]);
		if temp_spread[ori_eta[i][1]]=ori_eta[i][2] then
			Print("1");
		else
			Print("0");
		fi;
	od;
	Print("\n");

end;

########################################## Difficulties ###################################################

##
difficulty_tri:=function(L)

	local deg, number, num_vertices;

	deg:=degree(L);
	num_vertices:=Length(Set(Flat(L)));

	for number in deg do
		if number=3 then
			return 3*num_vertices;
		fi;
	od;

	for number in deg do
		if number=4 then
			return 3*num_vertices+1;
		fi;
	od;

	return 3*num_vertices+2;

end;


##
difficulty_bis:=function(bis)

	if difficulty_tri(bis[1])=difficulty_tri(bis[2]) then
		return 2*difficulty_tri(bis[1])+1;
	else return 2*Maximum(difficulty_tri(bis[1]),difficulty_tri(bis[2]));
	
	fi;

end;


##
difficulty_eta:=function(eta)

	local temp,counter;
	temp:=[];
	for counter in [1..Length(eta)-1] do
		Add(temp, difficulty_bis([eta[counter],eta[counter+1]]));
	od;
	
	return Maximum(temp);

end;

##
max_vertex_eta:=function(eta)

	local temp,counter;
	temp:=[];
	for counter in [1..Length(eta)] do
		temp[counter]:=Length(Set(Flat(eta[counter])));
	od;
	
	return Maximum(temp);
	
end;


######################################## Computing the cycle #################################################
#NOT USED#

cycle:=function(L)

	local temp, Lbis, vertices, edges, vertex, edge, simplex;
	
	Lbis:=[];;
	
	#find possible flips that lower the difficulty

	vertices:=ve_count(L)[1];
	edges:=ve_count(L)[2];
	
	if Length(L)<=4 then
		return 0;
	fi;
	
	for vertex in vertices do
		if Length(link(L, vertex)) = 3 then

			#modify L
			simplex:=Set(Flat(link(L,vertex)));
			
			Print(simplex, " ");
			Print(vertex, "\n");
			
			RemoveSet(L, Set([simplex[1],simplex[2],vertex[1]]));
			RemoveSet(L, Set([simplex[1],simplex[3],vertex[1]]));
			RemoveSet(L, Set([simplex[2],simplex[3],vertex[1]]));
			
			AddSet(L, simplex);

			return L;
			
		fi;
	od;
	
	temp:=degree(L);
	
	for edge in edges do
		
		if not IsSubset(Set(Flat(link(L,edge))),edges) then			
		
			#modify L
			simplex:=Set(Flat(link(L,edge)));
			
			Print(edge);
			Print(simplex);
			
			RemoveSet(L, Set([edge[1],edge[2],simplex[1]]));
			RemoveSet(L, Set([edge[1],edge[2],simplex[2]]));
			
			AddSet(L, Set([simplex[1],simplex[2],edge[1]]));
			AddSet(L, Set([simplex[1],simplex[2],edge[2]]));
			
			return L;
			
		fi;
	od;
	
end;	



recursion:=function(L)

	local i, Lbis, result, result2, recres, count, vertices, edges, vertex, edge, simplex, bis, l, temp, temprec, temprec2, recc;
	
	result:=[];;
	result2:=[];;
	Lbis:=[];;
	recres:=[];;
	count:=0;;
	temprec2:=[];;

	#find possible flips that lower the difficulty

	vertices:=ve_count(L)[1];
	edges:=ve_count(L)[2];
	
	if Length(L)=4 then
		return recres;
	fi;
	
	for vertex in vertices do
		if Length(link(L, vertex)) = 3 then

			#modify L
			Lbis:=ShallowCopy(L);
			simplex:=Set(Flat(link(L,vertex)));
			
			Print(simplex);
			Print(vertex);
			
			RemoveSet(Lbis, Set([simplex[1],simplex[2],vertex[1]]));
			RemoveSet(Lbis, Set([simplex[1],simplex[3],vertex[1]]));
			RemoveSet(Lbis, Set([simplex[2],simplex[3],vertex[1]]));
			
			AddSet(Lbis, simplex);
			
			#make the recursion
			
			AddSet(result, [Lbis,L]);
			AddSet(result2, Lbis);
			
			count:=count + 1;
			
		fi;
	od;
	
	temp:=degree(L);
	
	for edge in edges do
		
		if not IsSubset(Set(Flat(link(L,edge))),edges) then			###CHECK###
			#modify L
			Lbis:=ShallowCopy(L);
			simplex:=Set(Flat(link(L,edge)));
			
			Print(edge);
			Print(simplex);
			
			RemoveSet(Lbis, Set([edge[1],edge[2],simplex[1]]));
			RemoveSet(Lbis, Set([edge[1],edge[2],simplex[2]]));
			
			AddSet(Lbis, Set([simplex[1],simplex[2],edge[1]]));
			AddSet(Lbis, Set([simplex[1],simplex[2],edge[2]]));
			
			#result - bistellar flips
			#result2 - for the recursion
						
			if difficulty_tri(Lbis) < difficulty_tri(L) then
				
				AddSet(result, [Lbis,L]);
				AddSet(result2, Lbis);
						
				count:=count + 1;
					
			fi;
			
		fi;
	od;
	
	for bis in result do 
		recres[Position(result,bis)]:= rec( denom:=count , flip:=bis );
	od;
	
	for l in result2 do
	
		temprec:=recursion(l);
		temprec2:=[];
		for i in [1 .. Length(temprec)] do
			if temprec[i] <> [] then
				Add(temprec2, temprec[i]);;
			fi;
		od;
		
		temprec:=ShallowCopy(temprec2);;
		
		for recc in temprec do
			recc.denom:=count * recc.denom;
		od;
		Append(recres, temprec);
		
	od;
	
	return recres;
	
end;	


##
cycle_count:=function(bist)

	local j, k;
	
	vertices:=Set(Flat(faces));


	for k in [1..Length(bisfaces)-1] do
		sgn_eta[k]:=1;
	od;
	
	ori_eta[1]:=1;

	for j in [1..Length(vertices)] do
		for k in [1..Length(bisfaces)-1] do
			if (link(bisfaces[k], [vertices[j]])<>link(bisfaces[k+1], [vertices[j]])) and (Length(link(bisfaces[k+1], [vertices[j]]))>0) then
				Add(eta,[link(bisfaces[k], [vertices[j]]),link(bisfaces[k+1], [vertices[j]])]);
				Set(eta[k][1]);
				Set(eta[k][2]);
				#ORI_ETA ! ! ! Apparently not.
																
			fi;
		od;
	od;
	
	#for j in [1..Length(eta)] do
	#	ori_eta[j+1]:=ori_sub(eta[j][1][1],Intersection(eta[j][1][1], eta[j][2][1]));
	#od;
end;

########################################### Duplications and signs ##################################

##
sgn_eta_change:=function(etaa, sgn_etaa)

local temp, bis;
	for bis in etaa do
		if sgn_etaa[Position(bis,etaa)]=-1 then 
			temp:=ShallowCopy(bis[1]);
			bis[1]:=ShallowCopy(bis[2]);
			bis[2]:=temp;
			sgn_etaa[Position(bis,etaa)]:=1;
			Print("sgn_eta_change: ", Position(bis,etaa)," changed to positive");
		fi;
	od;

end;

##
duplicate_free_eta:=function(eta,ori_eta)

	# Remove consecutive cancelling pairs: whenever U([eta[b],eta[b+1]]) =
	# U([eta[b+1],eta[b+2]]) the middle element and its left neighbour are
	# removed.  Cancellations can cascade, so after each removal we step
	# back one position and recheck.
	#
	# Complexity: O(n) calls to U instead of the previous O(n^2).
	# All n-1 U-values are pre-computed once; after a removal only the
	# one new boundary value needs to be recomputed.

	local u, b;

	if Length(eta) < 3 then return; fi;

	# Pre-compute U for every consecutive pair.
	u:=List([1..Length(eta)-1], b -> U([eta[b],eta[b+1]]));

	b:=1;
	while b <= Length(eta)-2 do
		if u[b]=u[b+1] then
			Remove(eta,    b); Remove(eta,    b);
			Remove(ori_eta,b); Remove(ori_eta,b);
			Remove(u,      b); Remove(u,      b);
			# Recompute the one U-value that now spans across the gap.
			if b > 1 then
				u[b-1]:=U([eta[b-1],eta[b]]);
				b:=b-1;
			fi;
		else
			b:=b+1;
		fi;
	od;

end;



######################################## P, Q, R ######################################################

##

count_pq:=function(L, lu, ld, ru, rd, v)

	local i, j, edge, linkv, cycle, count, countp, countq, p, q;
	
	linkv:=link(L,[v]);
	cycle:=[];
	count:=0;
	
	cycle[1]:=linkv[1][1];
	
	for i in [1..Length(linkv)] do
		for edge in linkv do
			if cycle[i]=edge[1] and (i=1 or cycle[i-1]<>edge[2]) then 
				cycle[i+1]:=edge[2];
			fi;
			if cycle[i]=edge[2] and (i=1 or cycle[i-1]<>edge[1]) then 
				cycle[i+1]:=edge[1];
			fi;
		od;
	od;
	
	#Print("  count_pq: ->cycle:", cycle, "\n");
	
	Remove(cycle);
	
	if (Position(cycle,ru)>Position(cycle,rd) and Position(cycle,ld)>Position(cycle,lu)) or (Position(cycle,lu)>Position(cycle,ru) and Position(cycle,rd)>Position(cycle,ld)) then
		p:=(Position(cycle,lu)-Position(cycle,ru)) mod Length(cycle);
		q:=(Position(cycle,rd)-Position(cycle,ld)) mod Length(cycle);
	else
		p:=(Position(cycle,ru)-Position(cycle,lu)) mod Length(cycle);
		q:=(Position(cycle,ld)-Position(cycle,rd)) mod Length(cycle);
	fi;
	
	#Print("  count_pq: ->p=",p,", q=",q,"\n");
	
	return [p,q];	

end;

##
count_ro:=function(pq)

	local p,q;
	p:=pq[1];
	q:=pq[2];

	#Print("  count_ro: ->p=",p,", q=",q,", ",(q-p)/((p+q+2)*(p+q+3)*(p+q+4))," returned\n");
	
	return (q-p)/((p+q+2)*(p+q+3)*(p+q+4));

end;

##
count_omega:=function(p)

	#Print("  count_omega: ->p=",p,", ",1/((p+2)*(p+3))," returned\n");
	return 1/((p+2)*(p+3));
	
end;


### Special for b=3 ###

count_with_intersection:=function(bis,bis_edge,edge,ori1)

	local U1, U2, intersection, link_edge, link_bis_edge, temp_ori1, v, w, u, temp;
	
	link_bis_edge:=Set(Flat(link(bis[1],bis_edge)));
	U1:=U(bis);
	link_edge:=Set(Flat(link(bis[1],edge)));
	U2:=Set(Concatenation(edge,link_edge));
	
	temp_ori1:=ori_spread(bis[1],ori1);
	
	intersection:=Intersection(U1,U2);
	
	if Length(intersection)=0 then
	
		return 0;
		
	elif Length(intersection)=1 then
	
		v:=intersection[1];
		
		if v in link_bis_edge and v in link_edge then
			if simp_ori(bis[1],temp_ori1,[v,edge[2],edge[1]])=1 and simp_ori(bis[1],temp_ori1,[v,bis_edge[1],bis_edge[2]])=1 then
				return count_ro(count_pq(bis[1],bis_edge[2],bis_edge[1],edge[2],edge[1],v));
			elif simp_ori(bis[1],temp_ori1,[v,edge[2],edge[1]])=1 then
				return count_ro(count_pq(bis[1],bis_edge[1],bis_edge[2],edge[2],edge[1],v));
			elif simp_ori(bis[1],temp_ori1,[v,bis_edge[1],bis_edge[2]])=1 then
				return count_ro(count_pq(bis[1],bis_edge[2],bis_edge[1],edge[1],edge[2],v));
			elif simp_ori(bis[1],temp_ori1,[v,edge[2],edge[1]])=-1 and simp_ori(bis[1],temp_ori1,[v,bis_edge[1],bis_edge[2]])=-1 then
				return count_ro(count_pq(bis[1],bis_edge[1],bis_edge[2],edge[1],edge[2],v));
			fi;
		elif v in link_bis_edge then
			w:=Difference(edge,[v])[1];
			if simp_ori(bis[1],temp_ori1,[v,link_edge[1],w])=1 and simp_ori(bis[1],temp_ori1,[v,bis_edge[2],bis_edge[1]])=1 then
				return -count_ro(count_pq(bis[1],bis_edge[2],bis_edge[1],link_edge[2],link_edge[1],v));
			elif simp_ori(bis[1],temp_ori1,[v,link_edge[1],w])=1 then
				return -count_ro(count_pq(bis[1],bis_edge[1],bis_edge[2],link_edge[2],link_edge[1],v));
			elif simp_ori(bis[1],temp_ori1,[v,bis_edge[2],bis_edge[1]])=1 then
				return -count_ro(count_pq(bis[1],bis_edge[2],bis_edge[1],link_edge[1],link_edge[2],v));
			elif simp_ori(bis[1],temp_ori1,[v,link_edge[1],w])=-1 and simp_ori(bis[1],temp_ori1,[v,bis_edge[2],bis_edge[1]])=-1 then
				return -count_ro(count_pq(bis[1],bis_edge[1],bis_edge[2],link_edge[1],link_edge[2],v));
			fi;
		elif v in link_edge then
			w:=Difference(bis_edge,[v])[1];
			if simp_ori(bis[1],temp_ori1,[v,link_bis_edge[1],w])=1 and simp_ori(bis[1],temp_ori1,[v,edge[1],edge[2]])=1 then
				return count_ro(count_pq(bis[1],link_bis_edge[2],link_bis_edge[1],edge[2],edge[1],v));
			elif simp_ori(bis[1],temp_ori1,[v,link_bis_edge[1],w])=1 then
				return count_ro(count_pq(bis[1],link_bis_edge[2],link_bis_edge[1],edge[1],edge[2],v));
			elif simp_ori(bis[1],temp_ori1,[v,edge[1],edge[2]])=1 then
				return count_ro(count_pq(bis[1],link_bis_edge[1],link_bis_edge[2],edge[2],edge[1],v));
			elif simp_ori(bis[1],temp_ori1,[v,link_bis_edge[1],w])=-1 and simp_ori(bis[1],temp_ori1,[v,edge[1],edge[2]])=-1 then
				return count_ro(count_pq(bis[1],link_bis_edge[1],link_bis_edge[2],edge[1],edge[2],v));
			fi;
		elif v in edge and v in bis_edge then
			w:=Difference(bis_edge,[v])[1];
			u:=Difference(edge,[v])[1];
			if simp_ori(bis[1],temp_ori1,[w,link_bis_edge[1],v])=1 and simp_ori(bis[1],temp_ori1,[v,link_edge[1],u])=1 then
				return -count_ro(count_pq(bis[1],link_bis_edge[2],link_bis_edge[1],link_edge[2],link_edge[1],v));
			elif simp_ori(bis[1],temp_ori1,[w,link_bis_edge[1],v])=1 then
				return -count_ro(count_pq(bis[1],link_bis_edge[2],link_bis_edge[1],link_edge[1],link_edge[2],v));
			elif simp_ori(bis[1],temp_ori1,[v,link_edge[1],u])=1 then
				return -count_ro(count_pq(bis[1],link_bis_edge[1],link_bis_edge[2],link_edge[2],link_edge[1],v));
			elif simp_ori(bis[1],temp_ori1,[w,link_bis_edge[1],v])=-1 and simp_ori(bis[1],temp_ori1,[v,link_edge[1],u])=-1 then
				return -count_ro(count_pq(bis[1],link_bis_edge[1],link_bis_edge[2],link_edge[1],link_edge[2],v));
			fi;
		fi;
		
	elif Length(intersection)=2 then
		
		v:=intersection[1];
		w:=intersection[2];
		
		if w in edge and v in bis_edge then
			u:=Difference(edge, [w])[1];
			temp:=simp_ori(bis[1],temp_ori1,[w,v,u]);
			return -temp * (count_ro([0,Length(link(bis[1],[w]))-3])-count_ro([0,Length(link(bis[1],[v]))-3]));
		elif w in edge then
			u:=Difference(edge, [w])[1];
			temp:=simp_ori(bis[1],temp_ori1,[w,v,u]);
			return temp * (count_ro([0,Length(link(bis[1],[w]))-4])-count_ro([0,Length(link(bis[1],[v]))-2]));
		elif v in bis_edge then
			u:=Difference(edge, [v])[1];
			temp:=simp_ori(bis[1],temp_ori1,[w,v,u]);
			return -temp * (count_ro([0,Length(link(bis[1],[w]))-2])-count_ro([0,Length(link(bis[1],[v]))-4]));
		elif w in bis_edge and v in edge then
			u:=Difference(edge, [v])[1];
			temp:=simp_ori(bis[1],temp_ori1,[w,v,u]);
			return temp * (count_ro([0,Length(link(bis[1],[w]))-3])-count_ro([0,Length(link(bis[1],[v]))-3]));
		fi;
	fi;
	
	Print("ERROR!");
	return 0;

end;


######################################## Decomposition #################################################


##
# Every case chain in decomposition() is a closed list of configurations with
# no fallback branch.  When a configuration falls outside its list the function
# drops out of the "for i in max_pos" loop without a return, and GAP reports
# that far from the cause -- as "must return a value" at Pt:=Pt+decomposition(...)
# in Gamma2.g -- or, when another position of max_pos happens to return first,
# not at all: the peak is silently skipped and the run continues on a chain that
# was never decomposed.
#
# record_unhandled captures the configuration instead, so an uncovered case is
# reported where it occurs and stays available afterwards in unhandled_cases
# for deriving the missing case from the configurations that actually arise.

unhandled_cases:=[];

record_unhandled:=function(tag, i, eta, ori_eta, extra)

	local before, after, U_before, U_after, entry;

	if i > 1 then before:=StructuralCopy(eta[i-1]); else before:=fail; fi;
	if i < Length(eta) then after:=StructuralCopy(eta[i+1]); else after:=fail; fi;

	if before = fail then U_before:=fail; else U_before:=U([eta[i-1],eta[i]]); fi;
	if after  = fail then U_after :=fail; else U_after :=U([eta[i],eta[i+1]]); fi;

	entry:=rec( tag      := tag,
	            position := i,
	            before   := before,
	            at       := StructuralCopy(eta[i]),
	            after    := after,
	            ori      := StructuralCopy(ori_eta[i]),
	            degrees  := degree(eta[i]),
	            U_before := U_before,
	            U_after  := U_after,
	            extra    := extra );

	Add(unhandled_cases, entry);

	Print("### decomposition: unhandled case -- ",tag,"\n");
	Print("###   position i        = ",i,"\n");
	Print("###   U(eta[i-1],eta[i]) = ",U_before,"\n");
	Print("###   U(eta[i],eta[i+1]) = ",U_after,"\n");
	if U_before <> fail and U_after <> fail then
		Print("###   intersection      = ",IntersectionSet(U_before,U_after),"\n");
	fi;
	Print("###   degrees in eta[i] = ",entry.degrees,"\n");
	Print("###   extra             = ",extra,"\n");
	Print("###   recorded as unhandled_cases[",Length(unhandled_cases),"]\n");

	return entry;

end;

##

decomposition:=function(eta,ori_eta)

local counter, i, j, k, l, difficulty_eta, bis, temp, temp1, temp2, temp3, temp4, temp5, temp6, temp7, tempve, tempve1, tempp, tempq, tempr, tempk, temp_res, element, simplex, edge, vertex, vertex2, p, q, r, kk, s, t, temp_faces, temp_ori, deg_ff, deg_ress, deg_f, deg_res, max_pos, sigma1, sigma2, case, u, u1, u2, u3, v, v1, v2, v3, v4, w, w1, w2, w3, w4, w5;

difficulty_eta:=[];
deg_f:=[];
deg_res:=[];
max_pos:=[];

vertex2:=0;

for counter in [1..Length(eta)-1] do
	Add(difficulty_eta, difficulty_bis([eta[counter],eta[counter+1]]));
od;

max_pos:=PositionsProperty(difficulty_eta + 1 - Maximum(difficulty_eta) , IsPosInt);

Print("Max difficulty - ",Maximum(difficulty_eta),"\n");
Print("Positions - ", max_pos,"\n");

for i in max_pos do
	if (difficulty_eta[i] mod 6) = 1 then
		deg_f:=degree(eta[i]);
		deg_res:=degree(eta[i+1]);
		for j in [1..Maximum(Length(deg_f),Length(deg_res))] do
			if (deg_f[j]=3) and (deg_res[j]=3) then
				##here change eta - case 1 deg 3
				
				Print("b=1 -> case deg 3, vertex ", j,"\n");
				
				temp1:=Set(Flat(link(eta[i],[j])));
				temp:=[StructuralCopy(eta[i]),StructuralCopy(eta[i+1])];
				
				for simplex in eta[i] do
					if j in simplex then
						RemoveSet(temp[1],simplex);
						RemoveSet(temp[2],simplex);
					fi;
				od;
				
				AddSet(temp[1],temp1);
				AddSet(temp[2],temp1);
				
				InsertElement(eta,temp[1],i+1);
				InsertElement(eta,temp[2],i+2);
				
				#orientation
				
				InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
				InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
				
				#p,q,r if needed
				
				u:=IntersectionSet(Set(Flat(link(eta[i],[j]))),U(temp));
				if Length(u)=0 then
					# everything's great
					Print("decomposition -> return ",0,"\n");
					return 0;
				elif Length(u)=1 then
					
					# д
					
					# not so great
					
					Print("  ->intersection - 1 vertex - ",u[1],"\n");
					
					u:=u[1];
					
					if deg_f[u]<deg_res[u] then
					
						temp_ori:=ori_spread(eta[i],ori_eta[i]);
					
						temp:=Set(Flat(link(eta[i],Set([u,j]))));
						temp2:=IntersectionSet(U([eta[i+1],eta[i+2]]),Set(Flat(link(eta[i+1],[u]))));
						if simp_ori(eta[i],temp_ori,[j,u,temp[1]]) = 1 then
							if simp_ori(eta[i],temp_ori,[u,temp2[2],temp2[1]])=1 then
								temp_res:=count_ro(count_pq(eta[i],temp[1],temp[2],temp2[1],temp2[2],u));
								Print("decomposition -> return ",temp_res,"\n");
								return temp_res;
							else
								temp_res:=count_ro(count_pq(eta[i],temp[1],temp[2],temp2[2],temp2[1],u));
								Print("decomposition -> return ",temp_res,"\n");
								return temp_res;
							fi;
						else
							if simp_ori(eta[i],temp_ori,[u,temp2[2],temp2[1]])=1 then
								temp_res:=count_ro(count_pq(eta[i],temp[2],temp[1],temp2[1],temp2[2],u));
								Print("decomposition -> return ",temp_res,"\n");
								return temp_res;
							else
								temp_res:=count_ro(count_pq(eta[i],temp[2],temp[1],temp2[2],temp2[1],u));
								Print("decomposition -> return ",temp_res,"\n");
								return temp_res;
							fi;
						fi;
						
						## RETURN RO
						
					else
					
						temp_ori:=ori_spread(eta[i+3],ori_eta[i+3]);
						
						temp:=Set(Flat(link(eta[i+3],Set([u,j]))));
						temp2:=IntersectionSet(U([eta[i+1],eta[i+2]]),Set(Flat(link(eta[i+3],[u]))));
						if simp_ori(eta[i+3],temp_ori,[j,u,temp[1]]) = 1 then
							if simp_ori(eta[i+3],temp_ori,[u,temp2[2],temp2[1]])=1 then
								temp_res:=-count_ro(count_pq(eta[i],temp[1],temp[2],temp2[1],temp2[2],u));
								Print("decomposition -> return ",temp_res,"\n");
								return temp_res;
							else
								temp_res:=-count_ro(count_pq(eta[i],temp[1],temp[2],temp2[2],temp2[1],u));
								Print("decomposition -> return ",temp_res,"\n");
								return temp_res;
							fi;
						else
							if simp_ori(eta[i+3],temp_ori,[u,temp2[2],temp2[1]])=1 then
								temp_res:=-count_ro(count_pq(eta[i],temp[2],temp[1],temp2[1],temp2[2],u));
								Print("decomposition -> return ",temp_res,"\n");
								return temp_res;
							else
								temp_res:=-count_ro(count_pq(eta[i],temp[2],temp[1],temp2[2],temp2[1],u));
								Print("decomposition -> return ",temp_res,"\n");
								return temp_res;
							fi;
						fi;
						
						## RETURN RO
					fi;
										
				else
					# Length(u)=2, a bit better
					Print("  ->intersection - 2 vertices - ",u[1],", ",u[2],"\n");
					
					temp_ori:=ori_spread(eta[i],ori_eta[i]);
					
					if simp_ori(eta[i],temp_ori,[u[1],u[2],j]) = 1 then
						u1:=u[1];
						u2:=u[2];
					else
						u1:=u[2];
						u2:=u[1];
					fi;
					
					if deg_f[u1]<deg_res[u1] then
						#  e
						temp_res:=count_ro([0,Length(link(eta[i],[u2]))-4])+count_ro([0,Length(link(eta[i],[u1]))-3]);
						Print("decomposition -> return ",temp_res,"\n");
						return temp_res;
					else
						# -e
						temp_res:=-count_ro([0,Length(link(eta[i],[u1]))-4])-count_ro([0,Length(link(eta[i],[u2]))-3]);
						Print("decomposition -> return ",temp_res,"\n");
						return temp_res;
					fi;
					
				fi;	
				##
			fi;
		od;
		
		for j in [1..Maximum(Length(deg_f),Length(deg_res))] do
			if (deg_f[j]=3) and (deg_res[j]=4) then
				for k in [1..Maximum(Length(deg_f),Length(deg_res))] do
					if (deg_f[k]=4) and (deg_res[k]=3) then
						##here change eta case 1 deg 3,4
						
						#modify vertex j -> simplices
						
						#-2a
						
						Print("b=1 -> case deg 3-4, vertices ", j,", ", k, "\n");
						
						temp1:=[];
						temp:=[eta[i],eta[i+1]];
						
						temp2:=[StructuralCopy(eta[i]),StructuralCopy(eta[i+1])];
						
						temp1:=Set(Flat(link(eta[i],[j])));
						AddSet(temp2[1],temp1);
						
						for vertex in temp1 do
							temp3:=ShallowCopy(temp1);
							RemoveSet(temp3, vertex);
							AddSet(temp3, j);
							RemoveSet(temp2[1],temp3);
						od;
						
						#same for the vertex k
						
						temp1:=Set(Flat(link(eta[i+1],[k])));
						AddSet(temp2[2],temp1);
						
						for vertex in temp1 do
							temp3:=ShallowCopy(temp1);
							RemoveSet(temp3, vertex);
							AddSet(temp3, k);
							RemoveSet(temp2[2],Set(temp3));
						od;
						
						#empty simplex
						
						temp4:=ShallowCopy(temp2[1]);
						
						for simplex in temp2[1] do
							if k in simplex then
								RemoveSet(temp4,simplex);
							fi;
						od;
						
						AddSet(temp4, Set(Flat(link(temp2[1],[k]))));
						
						#now change eta
						#and orientation (STILL NOT DONE!) (finally done) (with ori_eta)
						#there should be an element with fixed position and orientation
						
						InsertElement(eta,temp2[1],i+1);
						InsertElement(eta,temp4,i+2);
						InsertElement(eta,temp2[2],i+3);
						
						#orientation
												
						InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
						InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
						InsertElement(ori_eta,ori_check([eta[i+2],eta[i+3]],ori_eta[i+2]),i+3);
				
						#count p,q,r
						
						temp_ori:=ori_spread(eta[i],ori_eta[i]);
						
						v:=IntersectionSet(link(eta[i],Set([j,k])),link(eta[i+4],Set([j,k])))[1][1];
												
						if simp_ori(eta[i],temp_ori,[j,k,v])=1 then
							tempp:=Difference(Set(Flat(link(eta[i],[j]))),Set([v,k]))[1];
							tempr:=Difference(Set(Flat(link(eta[i],[k]))),Set([tempp,v,j]))[1];

							p:=degree(eta[i+1])[tempp] - 2;
							q:=degree(eta[i+1])[v] - 2;
							r:=degree(eta[i+1])[tempr] - 2;
							
							temp_res:=-count_omega(p)+count_omega(q)-count_omega(r)+ 1/12;
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
							
						else 
							tempp:=Difference(Set(Flat(link(eta[i],[j]))),Set([v,k]))[1];
							tempr:=Difference(Set(Flat(link(eta[i],[k]))),Set([tempp,v,j]))[1];

							p:=degree(eta[i+1])[tempp] - 2;
							q:=degree(eta[i+1])[v] - 2;
							r:=degree(eta[i+1])[tempr] - 2;
							
							temp_res:=count_omega(p)-count_omega(q)+count_omega(r)- 1/12;
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						
						fi;
					fi;
				od;
			fi;
		od;
	fi;
	
	if (difficulty_eta[i] mod 6) = 2 then
		if difficulty_eta[i]=2*difficulty_tri(eta[i]) then
			
			#Now describing cases a-k
			
			tempve:=[ve_count(eta[i-1]),ve_count(eta[i])];
			tempve1:=[tempve[2], ve_count(eta[i+1])];
			
			for edge in Combinations(U([eta[i-1],eta[i]]), 2) do
				if edge in tempve[2][2] and not edge in tempve[1][2] and (Length(link(eta[i],[edge[1]]))=4 or Length(link(eta[i],[edge[2]]))=4) then
					sigma1:=edge;
				fi;
			od;
			
			for edge in Combinations(U([eta[i],eta[i+1]]), 2) do
				if edge in tempve1[1][2] and not edge in tempve1[2][2] and (Length(link(eta[i],[edge[1]]))=4 or Length(link(eta[i],[edge[2]]))=4) then
					sigma2:=edge;
				fi;
			od;
			
			if Length(IntersectionSet(sigma1,sigma2))=0 then
				#abcei
				if Length(IntersectionSet(link(eta[i],sigma1), link(eta[i],sigma2))) = 0 then
					#abe
					if Length(IntersectionSet(Flat(link(eta[i],sigma1)), sigma2)) = 0 then
						#b2a
						if Length(IntersectionSet(Flat(link(eta[i],sigma2)), sigma1)) = 0 then
							#a
							case:='a';
							Print("b=2 -> a\n");
						else
							#b2
							case:='2';
							Print("b=2 -> b2\n");
						fi;
					else
						#b1a
						if Length(IntersectionSet(Flat(link(eta[i],sigma2)), sigma1)) = 0 then
							#b1
							case:='1';
							Print("b=2 -> b1\n");
						else
							#e
							case:='e';
							Print("b=2 -> e\n");
						fi;
						
					fi;
					
				elif Length(IntersectionSet(link(eta[i],sigma1), link(eta[i],sigma2))) = 1 then
					#c
					case:='c';
					Print("b=2 -> c\n");
				else
					#i
					case:='i';
					Print("b=2 -> i\n");
				fi;
			else
				#dfghjk
				if Length(IntersectionSet(link(eta[i],sigma1), link(eta[i],sigma2))) = 0 then
					#dgh
					if Length(IntersectionSet(Flat(link(eta[i],sigma1)), sigma2)) = 0 then
						#d
						case:='d';
						Print("b=2 -> d\n");
					else
						#gh
						if degree(eta[i])[IntersectionSet(sigma1,sigma2)[1]] > 4 then
							#g
							case:='g';
							Print("b=2 -> g\n");
						else
							#h
							case:='h';
							Print("b=2 -> h\n");
						fi;
					fi;
				elif Length(IntersectionSet(link(eta[i],sigma1), link(eta[i],sigma2))) = 1 then
					#f
					case:='f';
					Print("b=2 -> f\n");
				else
					#jk
					if Set(Union(Difference(sigma1,sigma2),Difference(sigma2,sigma1))) in tempve[2][2] then
						#k
						case:='k';
						Print("b=2 -> k\n");
					else
						#j
						case:='j';
						Print("b=2 -> j\n");
					fi;							
				fi;
			fi;
			
			##
			
			if case='a' then
				
				# gamma(L,sigma1,sigma2) is correctly defined and the cycle induces 0
				
				temp:=[];
				
				temp1:=U([eta[i-1],eta[i]]);
				temp2:=U([eta[i],eta[i+1]]);
				
				for simplex in Combinations(temp1,3) do
					if not simplex in eta[i] then
						AddSet(temp,simplex);
					else
						RemoveSet(eta[i],simplex);
					fi;
				od;
				for simplex in Combinations(temp2,3) do
					if not simplex in eta[i] then
						AddSet(temp,simplex);
					else 
						RemoveSet(eta[i],simplex);
					fi;
				od;
				
				UniteSet(eta[i],temp);

				# orientation

				ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
				
				Print("decomposition -> return ",0,"\n");
				return 0;

			elif case='1' then
				
				# touching by one vertex in sigma2, but not in sigma1
				
				# p,q,r
				
				temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
				v:=IntersectionSet(U([eta[i-1],eta[i]]),U([eta[i],eta[i+1]]))[1];
				if simp_ori(eta[i],temp_ori,[sigma1[1],sigma1[2],v])=1 then
					w1:=sigma1[1];
					w2:=sigma1[2];
				else
					w1:=sigma1[2];
					w2:=sigma1[1];
				fi;
				
				if v=sigma2[1] then
					v1:=sigma2[2];
				else
					v1:=sigma2[1];
				fi;
				
				
				temp1:=Set(Flat(link(eta[i],Set([v,v1]))));
				if simp_ori(eta[i],temp_ori,[v,v1,temp1[1]])=1 then
					w3:=temp1[1];
					w4:=temp1[2];
				else
					w3:=temp1[2];
					w4:=temp1[1];
				fi;
				
				##
				
				temp:=[];
				
				temp1:=U([eta[i-1],eta[i]]);
				temp2:=U([eta[i],eta[i+1]]);
				
				for simplex in Combinations(temp1,3) do
					if not simplex in eta[i] then
						AddSet(temp,simplex);
					else 
						RemoveSet(eta[i],simplex);
					fi;
				od;
				for simplex in Combinations(temp2,3) do
					if not simplex in eta[i] then
						AddSet(temp,simplex);
					else 
						RemoveSet(eta[i],simplex);
					fi;
				od;
				
				UniteSet(eta[i],temp);
				
				# orientation
				
				ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
				
				# p,q,r
				
				temp_res:=count_ro(count_pq(eta[i],w1,w2,w3,w4,v));
				Print("decomposition -> return ",temp_res,"\n");
				return temp_res;
				
			elif case='2' then
				
				# touching by one vertex in sigma1, but not in sigma2
				
				# p,q,r
				
				temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
				v:=IntersectionSet(U([eta[i-1],eta[i]]),U([eta[i],eta[i+1]]))[1];
				if simp_ori(eta[i],temp_ori,[sigma2[1],sigma2[2],v])=1 then
					w1:=sigma2[1];
					w2:=sigma2[2];
				else
					w1:=sigma2[2];
					w2:=sigma2[1];
				fi;
				
				if v=sigma1[1] then
					v1:=sigma1[2];
				else
					v1:=sigma1[1];
				fi;
				
				
				temp1:=Set(Flat(link(eta[i],Set([v,v1]))));
				if simp_ori(eta[i],temp_ori,[v,v1,temp1[1]])=1 then
					w3:=temp1[1];
					w4:=temp1[2];
				else
					w3:=temp1[2];
					w4:=temp1[1];
				fi;
				
				##
				
				temp:=[];
				
				temp1:=U([eta[i-1],eta[i]]);
				temp2:=U([eta[i],eta[i+1]]);
				
				for simplex in Combinations(temp1,3) do
					if not simplex in eta[i] then
						AddSet(temp,simplex);
					else 
						RemoveSet(eta[i],simplex);
					fi;
				od;
				for simplex in Combinations(temp2,3) do
					if not simplex in eta[i] then
						AddSet(temp,simplex);
					else 
						RemoveSet(eta[i],simplex);
					fi;
				od;
				
				UniteSet(eta[i],temp);
										
				# orientation
				
				ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);

				# p,q,r
				
				temp_res:=count_ro(count_pq(eta[i],w4,w3,w2,w1,v));
				Print("decomposition -> return ",temp_res,"\n");
				return temp_res;
				
			elif case='d' then
			
				# touching in one vertex in sigma1 and in sigma2
				
				# p,q,r
				
				temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
				v:=IntersectionSet(sigma1,sigma2)[1];
				
				if v=sigma1[1] then
					v1:=sigma1[2];
				else
					v1:=sigma1[1];
				fi;
				
				if v=sigma2[1] then
					v2:=sigma2[2];
				else
					v2:=sigma2[1];
				fi;
				
				temp1:=Set(Flat(link(eta[i],sigma1)));
				temp2:=Set(Flat(link(eta[i],sigma2)));
				
				if simp_ori(eta[i],temp_ori,[v1,v,temp1[1]])=1 then
					w1:=temp1[1];
					w2:=temp1[2];
				else
					w1:=temp1[2];
					w2:=temp1[1];
				fi;
				
				if simp_ori(eta[i],temp_ori,[v,v2,temp2[1]])=1 then
					w3:=temp2[1];
					w4:=temp2[2];
				else
					w3:=temp2[2];
					w4:=temp2[1];
				fi;
				
				##
				
				temp:=[];
				
				temp1:=U([eta[i-1],eta[i]]);
				temp2:=U([eta[i],eta[i+1]]);
				
				for simplex in Combinations(temp1,3) do
					if not simplex in eta[i] then
						AddSet(temp,simplex);
					else 
						RemoveSet(eta[i],simplex);
					fi;
				od;
				for simplex in Combinations(temp2,3) do
					if not simplex in eta[i] then
						AddSet(temp,simplex);
					else 
						RemoveSet(eta[i],simplex);
					fi;
				od;
				
				UniteSet(eta[i],temp);
				
				# orientation
				
				ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
				
				# p,q,r
				
				temp_res:=-count_ro(count_pq(eta[i],w1,w2,w3,w4,v));
				Print("decomposition -> return ",temp_res,"\n");
				return temp_res;
					
			elif case='c' then
			
				# touching in one vertex not in sigma1 and not in sigma2
				
				# p,q,r
				
				temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
				v:= IntersectionSet(U([eta[i-1],eta[i]]),U([eta[i],eta[i+1]]))[1];
				
				if simp_ori(eta[i],temp_ori,[sigma1[1],sigma1[2],v])=1 then
					w1:=sigma1[1];
					w2:=sigma1[2];
				else
					w1:=sigma1[2];
					w2:=sigma1[1];
				fi;
				
				if simp_ori(eta[i],temp_ori,[sigma2[2],sigma2[1],v])=1 then
					w3:=sigma2[1];
					w4:=sigma2[2];
				else
					w3:=sigma2[2];
					w4:=sigma2[1];
				fi;
				
				##
				
				temp:=[];
				
				temp1:=U([eta[i-1],eta[i]]);
				temp2:=U([eta[i],eta[i+1]]);
				
				for simplex in Combinations(temp1,3) do
					if not simplex in eta[i] then
						AddSet(temp,simplex);
					else 
						RemoveSet(eta[i],simplex);
					fi;
				od;
				for simplex in Combinations(temp2,3) do
					if not simplex in eta[i] then
						AddSet(temp,simplex);
					else 
						RemoveSet(eta[i],simplex);
					fi;
				od;
				
				UniteSet(eta[i],temp);
				
				# orientation
				
				ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
				
				# p,q,r
				
				temp_res:=-count_ro(count_pq(eta[i],w1,w2,w3,w4,v));
				Print("decomposition -> return ",temp_res,"\n");
				return temp_res;
				
			elif case='e' then
				
				#      	          __ __
				# side touching  | /| /|
				#   		 |/_|/_|
				
				# p,q,r
				
				v1:=IntersectionSet(sigma1,U([eta[i],eta[i+1]]))[1];
				v2:=IntersectionSet(sigma2,U([eta[i-1],eta[i]]))[1];
				
				if Length(link(eta[i],[v1]))=4 and Length(link(eta[i],[v2]))=4 then
				
					Print("  ->special case\n");
									
					u1:=Difference(sigma1,[v1])[1];
					u2:=Difference(sigma2,[v2])[1];
					
#					if Set([u1,u2]) in ve_count(eta[i])[2] then
#					
#					fi;

					
					w1:=Difference(Set(Flat(link(eta[i],sigma1))),[v2])[1];
					w2:=Difference(Set(Flat(link(eta[i],sigma2))),[v1])[1];
					
					temp1:=ShallowCopy(eta[i-1]);
					
					RemoveSet(temp1, Set([v1,v2,w1]));
					RemoveSet(temp1, Set([v1,v2,u2]));
					RemoveSet(temp1, Set([v1,u2,w1]));
					AddSet(temp1, Set([w1,u2,v2]));
					
					temp2:=ShallowCopy(temp1);
					
					RemoveSet(temp2, Set([v2,u1,w1]));
					RemoveSet(temp2, Set([v2,w1,u2]));
					AddSet(temp2, Set([v2,u2,u1]));
					AddSet(temp2, Set([w1,u1,u2]));
					
					temp3:=ShallowCopy(temp2);
					
					RemoveSet(temp3, Set([w1,u1,u2]));
					AddSet(temp3, Set([w1,u1,v1]));
					AddSet(temp3, Set([w1,u2,v1]));
					AddSet(temp3, Set([u1,u2,v1]));
					
					temp4:=ShallowCopy(temp3);
					
					RemoveSet(temp4, Set([u1,u2,v2]));
					RemoveSet(temp4, Set([u2,v2,w2]));
					RemoveSet(temp4, Set([u1,v2,w2]));
					AddSet(temp4, Set([u1,u2,w2]));
					
					temp5:=ShallowCopy(temp4);
					
					RemoveSet(temp5, Set([u1,v1,u2]));
					RemoveSet(temp5, Set([u1,w2,u2]));
					AddSet(temp5, Set([u1,v1,w2]));
					AddSet(temp5, Set([u2,v1,w2]));
					
					# change eta
					
					eta[i]:=ShallowCopy(temp1);
					InsertElement(eta,temp2,i+1);
					InsertElement(eta,temp3,i+2);
					InsertElement(eta,temp4,i+3);
					InsertElement(eta,temp5,i+4);
					
					# orientation
					
					ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
					InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
					InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
					InsertElement(ori_eta,ori_check([eta[i+2],eta[i+3]],ori_eta[i+2]),i+3);
					InsertElement(ori_eta,ori_check([eta[i+3],eta[i+4]],ori_eta[i+3]),i+4);
					
					# p,q,r
					
					temp_ori:=ori_spread(eta[i-1],ori_eta[i-1]);
					
					temp1:=simp_ori(eta[i-1],temp_ori,[u1,w1,v2]);
					
					temp_res:=temp1 * (count_omega(Length(link(eta[i-1],[w1]))-3)-count_omega(Length(link(eta[i-1],[u1]))-1)-count_omega(Length(link(eta[i-1],[v2]))-3)+count_omega(Length(link(eta[i-1],[u2]))-2)-count_omega(Length(link(eta[i+5],[w2]))-3)+count_omega(Length(link(eta[i+5],[u2]))-1)+count_omega(Length(link(eta[i+5],[v1]))-3)-count_omega(Length(link(eta[i+5],[u1]))-2));
					Print("decomposition -> return ",temp_res,"\n");
					return temp_res;
					
				else
				
					temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
					w:=IntersectionSet(U([eta[i-1],eta[i]]),Set(Flat(link(eta[i],Set([v1,v2])))))[1];
				
					temp3:=simp_ori(eta[i],temp_ori,[v1,w,v2]);
										
					##
				
					temp:=[];
				
					temp1:=U([eta[i-1],eta[i]]);
					temp2:=U([eta[i],eta[i+1]]);
				
					for simplex in Combinations(temp1,3) do
						if not simplex in eta[i] then
							AddSet(temp,simplex);
						else 
							RemoveSet(eta[i],simplex);
						fi;
					od;
					for simplex in Combinations(temp2,3) do
						if not simplex in eta[i] then
							AddSet(temp,simplex);
						else 
							RemoveSet(eta[i],simplex);
						fi;
					od;
				
					UniteSet(eta[i],temp);
				
					# orientation
				
					ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
				
					# p,q,r
					
					temp_res:=temp3 * (-count_ro([0,Length(link(eta[i],[v1]))-3])+count_ro([0,Length(link(eta[i],[v2]))-3]));
					Print("decomposition -> return ",temp_res,"\n");
					return temp_res;
					
				fi;
				
			elif case='f' then
				
				#	          __ __
				# side touching  |\ | /|
				# 		 |_\|/_|
				
				# p,q,r
				
				temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
				v2:=IntersectionSet(sigma1,sigma2)[1];
				temp1:=IntersectionSet(U([eta[i-1],eta[i]]),U([eta[i],eta[i+1]]));
				RemoveSet(temp1,v2);
				v1:=temp1[1];
				
				w:=IntersectionSet(U([eta[i-1],eta[i]]),Set(Flat(link(eta[i],Set([v1,v2])))))[1];
				
				temp3:=simp_ori(eta[i],temp_ori,[v1,w,v2]);
				
				##
				
				temp:=[];
				
				temp1:=U([eta[i-1],eta[i]]);
				temp2:=U([eta[i],eta[i+1]]);
				
				for simplex in Combinations(temp1,3) do
					if not simplex in eta[i] then
						AddSet(temp,simplex);
					else
						RemoveSet(eta[i],simplex);
					fi;
				od;
				for simplex in Combinations(temp2,3) do
					if not simplex in eta[i] then
						AddSet(temp,simplex);
					else 
						RemoveSet(eta[i],simplex);
					fi;
				od;
				
				UniteSet(eta[i],temp);
			
				# orientation
				
				ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
				
				# p,q,r
				
				temp_res:=temp3 * (count_ro([0,Length(link(eta[i],[v1]))-4])-count_ro([0,Length(link(eta[i],[v2]))-2]));
				Print("decomposition -> return ",temp_res,"\n");
				return temp_res;
				
			elif case='g' then
			
				#	________
				#	\  /\  /
				#	 \/__\/
				
				# problems
				# two subcases here
				
				u:=Intersection(sigma1,sigma2)[1];
				v1:=Difference(sigma1,[u])[1];
				v2:=Difference(sigma2,[u])[1];
				w1:=Difference(Set(Flat(link(eta[i],Set([v1,v2])))),[u])[1];
				w2:=Difference(Set(Flat(link(eta[i],sigma1))),[v2])[1];
				w3:=Difference(Set(Flat(link(eta[i],sigma2))),[v1])[1];
				
				if not Set([u,w1]) in tempve[2][2] then
					
					# easy case
					
					Print("  ->easy case - u=",u,", v1=",v1,", v2=",v2,"\n");
					
					# p,q,r
					
					temp_ori:=ori_spread(eta[i],ori_eta[i]);
					
					tempp:=Length(link(eta[i],[w1]))-2;
					tempq:=Length(link(eta[i],[v1]))-2;
					tempr:=Length(link(eta[i],[u]))-2;
					tempk:=Length(link(eta[i],[w3]))-2;
					
					p:=Length(link(eta[i],[w2]))-2;
					q:=Length(link(eta[i],[u]))-2;
					r:=Length(link(eta[i],[v2]))-2;
					kk:=Length(link(eta[i],[w1]))-2;
					
					temp5:=simp_ori(eta[i],temp_ori,[v1,v2,u]);
					
					##
					
					temp:=ShallowCopy(eta[i-1]);
					
					RemoveSet(temp, Set([v1,v2,w2]));
					RemoveSet(temp, Set([v1,w1,w2]));
					RemoveSet(temp, Set([v1,v2,w1]));
					AddSet(temp, Set([v2,w1,w2]));
					
					temp1:=ShallowCopy(temp);
					
					RemoveSet(temp1, Set([u,v2,w2]));
					RemoveSet(temp1, Set([w1,v2,w2]));
					AddSet(temp1, Set([u,w1,v2]));
					AddSet(temp1, Set([u,w1,w2]));
					
					temp2:=ShallowCopy(temp1);
					
					RemoveSet(temp2, Set([u,w1,w2]));
					AddSet(temp2, Set([v1,u,w1]));
					AddSet(temp2, Set([v1,w1,w2]));
					AddSet(temp2, Set([v1,u,w2]));
					
					temp3:=ShallowCopy(temp2);
					
					RemoveSet(temp3, Set([v2,u,w1]));
					RemoveSet(temp3, Set([v2,w1,w3]));
					RemoveSet(temp3, Set([v2,u,w3]));
					AddSet(temp3, Set([u,w1,w3]));							
					
					temp4:=ShallowCopy(temp3);
					
					RemoveSet(temp4, Set([u,v1,w1]));
					RemoveSet(temp4, Set([u,w3,w1]));
					AddSet(temp4, Set([u,v1,w3]));
					AddSet(temp4, Set([w1,v1,w3]));
					
					# change eta
					
					eta[i]:=ShallowCopy(temp);
					InsertElement(eta,temp1,i+1);
					InsertElement(eta,temp2,i+2);
					InsertElement(eta,temp3,i+3);
					InsertElement(eta,temp4,i+4);
					
					# orientation
					
					ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
					InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
					InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
					InsertElement(ori_eta,ori_check([eta[i+2],eta[i+3]],ori_eta[i+2]),i+3);
					InsertElement(ori_eta,ori_check([eta[i+3],eta[i+4]],ori_eta[i+3]),i+4);
					
					# p,q,r
					
					temp_res:=temp5 * (count_omega(p)-count_omega(q)-count_omega(r)+count_omega(kk)+count_omega(tempp)-count_omega(tempq)-count_omega(tempr)+count_omega(tempk));
					Print("decomposition -> return ",temp_res,"\n");
					return temp_res;
				
				else								
					#hard one
					
					Print("  ->hard case\n");
					
					w4:=Set(Flat(link(eta[i-1],Set([u,w1]))))[1];
					w5:=Set(Flat(link(eta[i-1],Set([u,w1]))))[2];
					
					# p,q,r
					
					temp_ori:=ori_spread(eta[i],ori_eta[i]);
					
					temp7:=simp_ori(eta[i],temp_ori,[u,v1,v2]);
					
					if temp7 * simp_ori(eta[i],temp_ori,[u,w4,w1]) = 1 then
						u1:=w4;
						u2:=w5;
					else
						u1:=w5;
						u2:=w4;
					fi;
					
					
					temp_res:= -count_ro(count_pq(eta[i-1],w2,v2,u2,u1,u)) + count_ro(count_pq(eta[i],v1,w3,u2,u1,u));
					
					##
					
					temp5:=ShallowCopy(eta[i-1]);
					temp6:=ShallowCopy(eta[i+1]);
					
					RemoveSet(temp5,Set([u,w1,w5]));
					RemoveSet(temp5,Set([u,w4,w5]));
					AddSet(temp5,Set([u,w4,w5]));
					AddSet(temp5,Set([w1,w4,w5]));
					
					RemoveSet(temp6,Set([u,w1,w5]));
					RemoveSet(temp6,Set([u,w4,w5]));
					AddSet(temp6,Set([u,w4,w5]));
					AddSet(temp6,Set([w1,w4,w5]));
					
					temp:=ShallowCopy(temp5);
					
					RemoveSet(temp, Set([v1,v2,w2]));
					RemoveSet(temp, Set([v1,w1,w2]));
					RemoveSet(temp, Set([v1,v2,w1]));
					AddSet(temp, Set([v2,w1,w2]));
					
					temp1:=ShallowCopy(temp);
					
					RemoveSet(temp1, Set([u,v2,w2]));
					RemoveSet(temp1, Set([v1,v2,w2]));
					AddSet(temp1, Set([u,v1,v2]));
					AddSet(temp1, Set([u,v1,w2]));
					
					temp2:=ShallowCopy(temp1);
					
					RemoveSet(temp2, Set([u,w1,w2]));
					AddSet(temp2, Set([v1,u,w1]));
					AddSet(temp2, Set([v1,w1,w2]));
					AddSet(temp2, Set([v1,u,w2]));
					
					temp3:=ShallowCopy(temp2);
					
					RemoveSet(temp3, Set([v2,u,w1]));
					RemoveSet(temp3, Set([v2,w1,w3]));
					RemoveSet(temp3, Set([v2,u,w3]));
					AddSet(temp3, Set([u,w1,w3]));							
					
					temp4:=ShallowCopy(temp3);
					
					RemoveSet(temp4, Set([u,v1,w1]));
					RemoveSet(temp4, Set([u,w3,w1]));
					AddSet(temp4, Set([u,v1,w3]));
					AddSet(temp4, Set([w1,v1,w3]));
					
					# change eta
					
					eta[i]:=ShallowCopy(temp5);
					InsertElement(eta,temp,i+1);
					InsertElement(eta,temp1,i+2);
					InsertElement(eta,temp2,i+3);
					InsertElement(eta,temp3,i+4);
					InsertElement(eta,temp4,i+5);
					InsertElement(eta,temp6,i+6);
										
					# orientation
					
					ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
					InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
					InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
					InsertElement(ori_eta,ori_check([eta[i+2],eta[i+3]],ori_eta[i+2]),i+3);
					InsertElement(ori_eta,ori_check([eta[i+3],eta[i+4]],ori_eta[i+3]),i+4);
					InsertElement(ori_eta,ori_check([eta[i+4],eta[i+5]],ori_eta[i+4]),i+5);
					InsertElement(ori_eta,ori_check([eta[i+5],eta[i+6]],ori_eta[i+5]),i+6);
					
					# p,q,r
					
					tempp:=Length(link(eta[i+7],[w1]))-2;
					tempq:=Length(link(eta[i+7],[v1]))-3;
					tempr:=Length(link(eta[i+7],[u]))-1;
					tempk:=Length(link(eta[i+7],[w3]))-3;
					
					p:=Length(link(eta[i-1],[w2]))-3;
					q:=Length(link(eta[i-1],[u]))-1;
					r:=Length(link(eta[i-1],[v2]))-3;
					kk:=Length(link(eta[i-1],[w1]))-2;
					
					temp_res:=temp5 * (temp_res + count_omega(p)-count_omega(q)-count_omega(r)+count_omega(kk)-count_omega(tempp)+count_omega(tempq)+count_omega(tempr)-count_omega(tempk));
					Print("decomposition -> return ",temp_res,"\n");
					return temp_res;
				
				fi;
				
			elif case='h' then
			
				#	 ____
				#	|\  /|
				#	| \/ |
				#	|1/\2|
				#	|/__\|
				
				u:=IntersectionSet(sigma1,sigma2)[1];
				v1:=Difference(sigma1,[u])[1];
				v2:=Difference(sigma2,[u])[1];
				w1:=Difference(Set(Flat(link(eta[i],sigma1))),[v2])[1];
				w2:=Difference(Set(Flat(link(eta[i],sigma2))),[v1])[1];
				
				# p,q,r
				
				temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
				temp4:=simp_ori(eta[i],temp_ori,[u,v1,v2]);
				
				##
				
				temp1:=Set(Flat(link(eta[i-1],[u])));		#k
				temp2:=StructuralCopy(eta[i-1]);
				
				for simplex in eta[i-1] do
					if u in simplex then
						RemoveSet(temp2, simplex);
					fi;
				od;
				AddSet(temp2,temp1);
				
				eta[i]:=StructuralCopy(temp2);
				
				temp1:=Set(Flat(link(eta[i+1],[u])));		#i
				temp2:=ShallowCopy(eta[i+1]);
				
				for simplex in eta[i+1] do
					if u in simplex then
						RemoveSet(temp2, simplex);
					fi;
				od;
				AddSet(temp2,temp1);
				
				# temp2 замыкает цикл
				
				InsertElement(eta,temp2,i+1);
				
				# orientation
				
				ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
				InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
				
				# p,q,r
				
				temp_res:=-temp4 * (count_omega(Length(link(eta[i-1],[w2]))-2)-count_omega(Length(link(eta[i-1],[v2]))-3)-count_omega(Length(link(eta[i-1],[v1]))-1)+count_omega(Length(link(eta[i-1],[w1]))-3));
				Print("decomposition -> return ",temp_res,"\n");
				return temp_res;
			
			elif case='i' then
			
				if degree(eta[i])[sigma1[1]] = 4 then 
					v1:=sigma1[1];
					u1:=sigma1[2];
				else
					v1:=sigma1[2];
					u1:=sigma1[1];
				fi;
				
				# p,q,r
				
				temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
				if simp_ori(eta[i],temp_ori,[u1,v1,Set(Flat(link(eta[i], sigma1)))[1]])=1 then
					w1:=Set(Flat(link(eta[i], sigma1)))[1];
					w2:=Set(Flat(link(eta[i], sigma1)))[2];
				else
					w1:=Set(Flat(link(eta[i], sigma1)))[2];
					w2:=Set(Flat(link(eta[i], sigma1)))[1];
				fi;
				
				for element in Set(Flat(link(eta[i],[v1]))) do
					if element<>w1 and element<>w2 and element<>u1 then
						w3:=element;
					fi;
				od;
				
				if simp_ori(eta[i],temp_ori,[sigma2[1],sigma2[2],w1])=1 then
					v2:=sigma2[1];
					u2:=sigma2[2];
				else
					v2:=sigma2[2];
					u2:=sigma2[1];
				fi;
				
				temp_res:= count_omega(Length(link(eta[i],[w2]))-2)-count_omega(Length(link(eta[i],[u1]))-2)-count_omega(Length(link(eta[i],[w1]))-2)+count_omega(Length(link(eta[i],[w3]))-2);
				
				##
				
				temp:=ShallowCopy(eta[i-1]);
				
				RemoveSet(temp,Set([w1,v1,w3]));
				RemoveSet(temp,Set([w1,v1,w2]));

				RemoveSet(temp,Set([w2,v1,w3]));
				AddSet(temp,Set([w1,w2,w3]));
				
				temp1:=ShallowCopy(temp);
				
				RemoveSet(temp1,Set([w1,w2,w3]));
				RemoveSet(temp1,Set([u1,w1,w2]));
				AddSet(temp1,Set([w1,w3,u1]));
				AddSet(temp1,Set([u1,w3,w2]));
				
				temp2:=ShallowCopy(temp1);
				
				AddSet(temp2,Set([u1,v1,w3]));
				AddSet(temp2,Set([u1,v1,w2]));
				AddSet(temp2,Set([w2,v1,w3]));
				RemoveSet(temp2,Set([u1,w2,w3]));
				
				temp3:=ShallowCopy(eta[i+1]);
				
				AddSet(temp3,Set([u1,v1,w3]));
				AddSet(temp3,Set([u1,w1,w3]));
				RemoveSet(temp3,Set([u1,v1,w1]));
				RemoveSet(temp3,Set([w1,v1,w3]));
				
				# so hard - now change eta
				
				eta[i]:=ShallowCopy(temp);
				InsertElement(eta,temp1,i+1);
				InsertElement(eta,temp2,i+2);
				InsertElement(eta,temp3,i+3);
				
				# orientation - new flips - in the end of eta (!)
				
				ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
				InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
				InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
				InsertElement(ori_eta,ori_check([eta[i+2],eta[i+3]],ori_eta[i+2]),i+3);
										
				# p,q,r
				
				if w3=v2 then
					Print("  ->w3=v2\n");
					temp_res:=temp_res - count_ro([0,Length(link(eta[i-1],[w1]))-4]) + count_ro([0,1]);
					Print("decomposition -> return ",temp_res,"\n");
					return temp_res;
				else
					temp_res:=temp_res + count_ro(count_pq(eta[i+2],u1,w3,u2,v2,w1));
					Print("decomposition -> return ",temp_res,"\n");
					return temp_res;
				fi;
								
			elif case='j' then
			
				v:=IntersectionSet(sigma1,sigma2)[1];
				v1:=Difference(sigma1,[v])[1];
				v2:=Difference(sigma2,[v])[1];
				temp:=Set(Flat(link(eta[i],sigma1)));
				
				# p,q,r
				
				temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
				if simp_ori(eta[i],temp_ori,[v,temp[2],v2])=1 then
					u1:=temp[1];
					u2:=temp[2];
				else
					u1:=temp[2];
					u2:=temp[1];
				fi;
				
				##
				
				RemoveSet(eta[i],Set([v,v1,u1]));
				RemoveSet(eta[i],Set([v,v2,u1]));
				RemoveSet(eta[i],Set([v,v2,u2]));
				RemoveSet(eta[i],Set([v,v1,u2]));
				
				AddSet(eta[i],Set([u2,u1,v2]));
				AddSet(eta[i],Set([u2,u1,v1]));
				
				# orientation
				
				ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
			
				# much hard
				
				# p,q,r
				
				temp_res:=2*count_omega(Length(link(eta[i-1],[u2]))-3)-2*count_omega(Length(link(eta[i-1],[u1]))-3);
				Print("decomposition -> return ",temp_res,"\n");
				return temp_res;
				
			elif case='k' then
			
				
				v:=IntersectionSet(sigma1,sigma2)[1];
				u1:=Set(Union(Difference(sigma1,sigma2),Difference(sigma2,sigma1)))[1];
				u2:=Set(Union(Difference(sigma1,sigma2),Difference(sigma2,sigma1)))[2];
				
				# p,q,r + spreading orientation
				
				temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
				if simp_ori(eta[i],temp_ori,[Set(Flat(link(eta[i],Set([u1,u2]))))[1],u1,u2])=1 then
					w3:=Set(Flat(link(eta[i],Set([u1,u2]))))[1];
					w4:=Set(Flat(link(eta[i],Set([u1,u2]))))[2];
				else
					w3:=Set(Flat(link(eta[i],Set([u1,u2]))))[2];
					w4:=Set(Flat(link(eta[i],Set([u1,u2]))))[1];
				fi;
				
				if simp_ori(eta[i],temp_ori,[Set(Flat(link(eta[i],Set([u1,v]))))[1],u1,v])=1 then
					w1:=Set(Flat(link(eta[i],Set([u1,v]))))[1];
					w2:=Set(Flat(link(eta[i],Set([u2,v]))))[2];
				else
					w1:=Set(Flat(link(eta[i],Set([u1,v]))))[2];
					w2:=Set(Flat(link(eta[i],Set([u2,v]))))[1];
				fi;
				
				##
				
				temp:=ShallowCopy(eta[i-1]);
				temp1:=ShallowCopy(eta[i+1]);
				temp2:=ShallowCopy(eta[i]);
				
				RemoveSet(temp, Set([u1,w3,w4]));
				RemoveSet(temp, Set([u2,w3,w4]));
				AddSet(temp, Set([u1,u2,w3]));
				AddSet(temp, Set([u1,u2,w4]));
				
				RemoveSet(temp1, Set([u1,w3,w4]));
				RemoveSet(temp1, Set([u2,w3,w4]));
				AddSet(temp1, Set([u1,u2,w3]));
				AddSet(temp1, Set([u1,u2,w4]));
				
				RemoveSet(temp2, Set([u1,w3,w4]));
				RemoveSet(temp2, Set([u2,w3,w4]));
				AddSet(temp2, Set([u1,u2,w3]));
				AddSet(temp2, Set([u1,u2,w4]));
				
				# so now case j on temp -> temp2 -> temp1
				
				RemoveSet(temp2, Set([u1,w1,v]));
				RemoveSet(temp2, Set([u1,w2,v]));
				RemoveSet(temp2, Set([u2,w1,v]));
				RemoveSet(temp2, Set([u2,w2,v]));
				AddSet(temp2, Set([u1,w1,w2]));
				AddSet(temp2, Set([u2,w1,w2]));
				
				# modify eta
				
				eta[i]:=temp;
				InsertElement(eta,temp2,i+1);
				InsertElement(eta,temp1,i+2);
				
				
				# orientation
				
				ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
				InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
				InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
				
				# p,q,r
				
				# з , -з, 2б, 2б
				
				temp_res:=count_ro(count_pq(eta[i-1],w2,w1,w3,w4,u1)) - count_ro(count_pq(eta[i-1],w3,w4,w2,w1,u2)) + 2*count_omega(Length(link(eta[i],[w2]))-3) - 2*count_omega(Length(link(eta[i],[w1]))-3);
				Print("decomposition -> return ",temp_res,"\n");
				return temp_res;
				
			fi;
			
		fi;
		
	#done

	fi;

	if (difficulty_eta[i] mod 6) = 3 then
		deg_f:=degree(eta[i]);
		deg_res:=degree(eta[i+1]);
		for j in [1..Maximum(Length(deg_f),Length(deg_res))] do
			if (deg_f[j]=4) and (deg_res[j]=4) then
				##here change eta - case 3 deg 4
				
				Print("b=3 -> deg 4, j=",j,"\n");
				
				temp_faces:=[[],[]];
				
				temp2:=Set(Flat(link(eta[i], [j])));
				temp3:=[StructuralCopy(eta[i]),StructuralCopy(eta[i+1])];
				temp_faces[1]:=ve_count(eta[i]);
				temp_faces[2]:=ve_count(eta[i+1]);
				
				for edge in Combinations(Set(Flat(link(eta[i],[j]))),2) do
					if not edge in temp_faces[1][2] and not edge in temp_faces[2][2] then
						# flip from edge
						u1:=Difference(temp2,edge)[1];
						u3:=Difference(temp2,edge)[2];

						RemoveSet(temp3[1], Set([edge[1],u1,j]));
						RemoveSet(temp3[1], Set([edge[2],u1,j]));
						AddSet(temp3[1], Set([edge[1],edge[2],u1]));
						AddSet(temp3[1], Set([edge[1],edge[2],j]));

						RemoveSet(temp3[2], Set([edge[1],u1,j]));
						RemoveSet(temp3[2], Set([edge[2],u1,j]));
						AddSet(temp3[2], Set([edge[1],edge[2],u1]));
						AddSet(temp3[2], Set([edge[1],edge[2],j]));

						break;
					fi;
				od;

 				InsertElement(eta,temp3[1],i+1);
 				InsertElement(eta,temp3[2],i+2);
 				
 				#and don't forget about the orientation  HERE!
 				
 				InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
 				InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
 				
 				#p,q,r ??
 				
 				temp_ori:=ori_spread(eta[i+1],ori_eta[i+1]);
 				
 				temp:=Flat(link(eta[i],Set([j,u1])));
 				
 				if simp_ori(eta[i+1],temp_ori,[temp[1],temp[2],j])=1 then
 					v1:=temp[1];
 					v2:=temp[2];
 				else
					v2:=temp[1];
					v1:=temp[2];
				fi;
				
				temp:=IntersectionSet(U([eta[i],eta[i+1]]),U([eta[i+1],eta[i+2]]));
				temp1:=U([eta[i+1],eta[i+2]]);
				
				if Length(temp)=0 then
				
					Print("decomposition -> return ",0,"\n");
					return 0;
				
				elif temp=[v1] then
				
					Print("  ->intersection - v1\n");
 				
					if deg_f[v1]<deg_res[v1] then
						temp2:=IntersectionSet(Set(Flat(link(eta[i],[v1]))),U([eta[i+1],eta[i+2]]));
						if simp_ori(eta[i+1],temp_ori,[temp2[1],v1,temp2[2]])=1 then
							#COUNT->RETURN
							temp_res:=count_ro(count_pq(eta[i],temp2[2],temp2[1],j,u1,v1));
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						else
							#COUNT->RETURN
							temp_res:=count_ro(count_pq(eta[i],temp2[1],temp2[2],j,u1,v1));
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						fi;												
					else
						temp2:=IntersectionSet(Set(Flat(link(eta[i+3],[v1]))),U([eta[i+1],eta[i+2]]));
						
						temp3:=IntersectionSet(Set(Flat(link(eta[i],[v1]))),U([eta[i+1],eta[i+2]]));

						RemoveSet(temp3, temp2[1]);
						RemoveSet(temp3, temp2[2]);
						temp3:=temp3[1];
						
						if simp_ori(eta[i+1],temp_ori,[temp3,v1,temp2[1]])=1 then
							#COUNT->RETURN
							temp_res:=-count_ro(count_pq(eta[i],temp2[1],temp2[2],j,u1,v1));
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						else
							#COUNT->RETURN
							temp_res:=-count_ro(count_pq(eta[i],temp2[2],temp2[1],j,u1,v1));
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						fi;										
					fi;
				
 				elif temp=[u1] then
 				
 					Print("  ->intersection - u1\n");
 				
 					if deg_f[u1]<deg_res[u1] then
						temp2:=IntersectionSet(Set(Flat(link(eta[i],[u1]))),U([eta[i+1],eta[i+2]]));
						if simp_ori(eta[i+1],temp_ori,[temp2[1],u1,temp2[2]])=1 then
							#COUNT->RETURN
							temp_res:=-count_ro(count_pq(eta[i],temp2[2],temp2[1],v1,v2,u1));
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						else
							#COUNT->RETURN
							temp_res:=-count_ro(count_pq(eta[i],temp2[1],temp2[2],v1,v2,u1));
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						fi;												
					else
						temp2:=IntersectionSet(Set(Flat(link(eta[i+3],[u1]))),U([eta[i+1],eta[i+2]]));
						
						temp3:=IntersectionSet(Set(Flat(link(eta[i],[u1]))),U([eta[i+1],eta[i+2]]));
						RemoveSet(temp3, u1);
						RemoveSet(temp3, temp2[1]);
						RemoveSet(temp3, temp2[2]);
						temp3:=temp3[1];
						
						if simp_ori(eta[i+1],temp_ori,[temp3,u1,temp2[1]])=1 then
							#COUNT->RETURN
							temp_res:=count_ro(count_pq(eta[i],temp2[1],temp2[2],v1,v2,u1));
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						else
							#COUNT->RETURN
							temp_res:=count_ro(count_pq(eta[i],temp2[2],temp2[1],v1,v2,u1));
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						fi;										
					fi;
				
				elif temp=[v2] then
					
					Print("  ->intersection - v2\n");

					if deg_f[v2]<deg_res[v2] then
						temp2:=IntersectionSet(Set(Flat(link(eta[i],[v2]))),U([eta[i+1],eta[i+2]]));
						if simp_ori(eta[i+1],temp_ori,[temp2[1],v2,temp2[2]])=1 then
							#COUNT->RETURN
							temp_res:=count_ro(count_pq(eta[i],temp2[2],temp2[1],u1,j,v2));
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						else
							#COUNT->RETURN
							temp_res:=count_ro(count_pq(eta[i],temp2[1],temp2[2],u1,j,v2));
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						fi;												
					else
						temp2:=IntersectionSet(Set(Flat(link(eta[i+3],[v2]))),U([eta[i+1],eta[i+2]]));
						
						temp3:=IntersectionSet(Set(Flat(link(eta[i],[v2]))),U([eta[i+1],eta[i+2]]));
						RemoveSet(temp3, v2);
						RemoveSet(temp3, temp2[1]);
						RemoveSet(temp3, temp2[2]);
						temp3:=temp3[1];
						
						if simp_ori(eta[i+1],temp_ori,[temp3,v2,temp2[1]])=1 then
							#COUNT->RETURN
							temp_res:=-count_ro(count_pq(eta[i],temp2[1],temp2[2],u1,j,v2));
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						else
							#COUNT->RETURN
							temp_res:=-count_ro(count_pq(eta[i],temp2[2],temp2[1],u1,j,v2));
							Print("decomposition -> return ",temp_res,"\n");
							return temp_res;
						fi;										
					fi;
 				
 				elif temp=Set([u1,v2]) then
 				
 					Print("  ->intersection - [u1,v2]\n");
 					
 					if deg_f[u1]<deg_res[u1] then
 				        	tempq:=deg_f[u1]-3;
 				        	tempp:=deg_f[v2]-3;
 				        	
 					 	temp_res:=count_ro([0,tempq])-count_ro([0,tempp]);
 				        	Print("decomposition -> return ",temp_res,"\n");
 				        	return temp_res;
 					else
 						tempq:=deg_f[u1]-4;
 				        	tempp:=deg_f[v2]-2;
 				        	
 				        	temp_res:=-count_ro([0,tempq])+count_ro([0,tempp]);
 				        	Print("decomposition -> return ",temp_res,"\n");
 				        	return temp_res;
 					fi;

 				elif temp=Set([u1,v1]) then
 					
 					Print("  ->intersection - [u1,v1]\n");
 					
 					if deg_f[u1]<deg_res[u1] then
 				        	tempq:=deg_f[v1]-3;
 				        	tempp:=deg_f[u1]-3;
 				        	
 				        	temp_res:=count_ro([0,tempq])-count_ro([0,tempp]);
 				        	Print("decomposition -> return ",temp_res,"\n");		        	
 				        	return temp_res;
 					else
 						tempq:=deg_f[v1]-2;
 				        	tempp:=deg_f[u1]-4;
 				        	
 				        	temp_res:=-count_ro([0,tempq])+count_ro([0,tempp]);
 				        	Print("decomposition -> return ",temp_res,"\n"); 				        	
 				        	return temp_res;
 					fi;
 				
 				fi;
			fi;
		od;
		
		for j in [1..Maximum(Length(deg_f),Length(deg_res))] do
			if (deg_f[j]=4) and (deg_res[j]=5) then
				for k in [1..Maximum(Length(deg_f),Length(deg_res))] do
					if (deg_f[k]=5) and (deg_res[k]=4) then
						##here change eta case 3 deg 4,5
						
						Print("b=3 -> deg 4-5 - k=",k,", j=",j,"\n");
						
						temp:=Set(Flat(link(eta[i],[j])));
						UniteSet(temp,link(eta[i],[k]));
						tempve:=ve_count(eta[i]);
						
						for w in [1..Length(deg_f)] do
							if deg_f[w]=5 and not w in temp then
								
								#find the flip
								for edge in Combinations(Set(Flat(link(eta[i],[w]))),2) do
									if not edge in tempve[2] then
										temp1:=edge;
									fi;
								od;
								
								for vertex in Set(Flat(link(eta[i],[w]))) do
									if Set([w,temp1[1],vertex]) in eta[i] and Set([w,temp1[2],vertex]) in eta[i] then
										temp2:=vertex;
										break;
									fi;
								od;
								
								#now do the first cycle
								temp3:=ShallowCopy(eta[i]);
								
								RemoveSet(temp3, Set([w, temp2, temp1[1]]));
								RemoveSet(temp3, Set([w, temp2, temp1[2]]));
								
								AddSet(temp3, Set([w, temp1[1], temp1[2]]));
								AddSet(temp3, Set([temp2, temp1[1], temp1[2]]));
								
								temp4:=ShallowCopy(temp3);
								
								RemoveSet(temp4, Set([w, temp2, temp1[1]]));
								RemoveSet(temp4, Set([w, temp2, temp1[2]]));
								
								AddSet(temp4, Set([w, temp1[1], temp1[2]]));
								AddSet(temp4, Set([temp2, temp1[1], temp1[2]]));
								
								# Change eta
								
								InsertElement(eta,temp3,i+1);
								InsertElement(eta,temp4,i+2);
								
								#orientation after the first cycle
								
 								InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
 								InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
 				
								
								#MORE OF THIS HERE
								#and count p,q,r also
								#variables reused (temp3)
								
								temp_res:=0;
								
								temp_ori:=ori_spread(eta[i],ori_eta[i]);
								
								if simp_ori(eta[i],temp_ori,[temp2,temp1[1],w])=1 then
									w1:=temp1[1];
									w2:=temp1[2];
								else
									w1:=temp1[2];
									w2:=temp1[1];
								fi;
								
								v1:=IntersectionSet(U([eta[i+1],eta[i+2]]),Set(Flat(link(eta[i+1],Set([j,k])))))[1];
								v2:=IntersectionSet(U([eta[i+1],eta[i+2]]),Set(Flat(link(eta[i+2],Set([j,k])))))[1];
								temp3:=IntersectionSet(Set([w1,w2,w,temp2]),Set([v1,v2]));
								
								if Length(temp3)=0 then
								
									temp_res:=0;
								
								elif temp3=[v1] then
								
									if simp_ori(eta[i],temp_ori,[v1,k,j])=1 then
										if w2=v1 then
											temp_res:=count_ro(count_pq(eta[i],temp2,w,j,v2,w2));
										elif w1=v1 then
											temp_res:=-count_ro(count_pq(eta[i],v2,j,temp2,w,w1));
										elif temp2=v1 then
											temp_res:=-count_ro(count_pq(eta[i],w1,w2,j,v2,temp2));
										fi;
										
									else
										
										if w2=v1 then
											temp_res:=count_ro(count_pq(eta[i],temp2,w,v2,j,w2));
										elif w1=v1 then
											temp_res:=-count_ro(count_pq(eta[i],j,v2,temp2,w,w1));
										elif temp2=v1 then
											temp_res:=-count_ro(count_pq(eta[i],w1,w2,v2,j,temp2));
										fi;
									fi;
								
								elif temp3=[v2] then
								
									if simp_ori(eta[i],temp_ori,[v1,k,j])=1 then
										if w2=v2 then
											temp_res:=count_ro(count_pq(eta[i],temp2,w,v1,k,w2));
										elif w1=v2 then
											temp_res:=count_ro(count_pq(eta[i],w,temp2,v1,k,w1));
										elif temp2=v2 then
											temp_res:=count_ro(count_pq(eta[i],w1,w2,v1,k,temp2));
										fi;
										
									else
										
										if w2=v2 then
											temp_res:=count_ro(count_pq(eta[i],temp2,w,k,v1,w2));
										elif w1=v2 then
											temp_res:=count_ro(count_pq(eta[i],w,temp2,k,v1,w1));
										elif temp2=v2 then
											temp_res:=count_ro(count_pq(eta[i],w1,w2,k,v1,temp2));
										fi;
									fi;
								
								elif temp3=Set([v1,v2]) then
								
									if temp2=v1 and w2=v2 then
										temp_res:=count_ro([0,deg_f[temp2]-4])-count_ro([0,deg_f[w2]-2]);
									elif w1=v1 then
										temp_res:=-count_ro([0,deg_f[w1]-3])+count_ro([0,deg_f[temp2]-3]);
									elif w2=v2 then
										temp_res:=-count_ro([0,deg_f[temp2]-3])+count_ro([0,deg_f[w2]-3]);
									elif temp2=v1 and w1=v2 then
										temp_res:=count_ro([0,deg_f[w1]-2])-count_ro([0,deg_f[temp2]-4]);
									fi;
								
								fi;
								
								u:=temp2;
								
								#now redo the case above
								#variables are reused
								
								temp:=[eta[i+1],eta[i+2]];
								temp2:=Set(Flat(link(temp[1], [w])));
								temp3:=ShallowCopy(temp);
								
								for edge in Combinations(Set(Flat(link(eta[i+1],[w]))),2) do
									if not edge in eta[i+1] and not edge in eta[i+2] then
										# flip from edge
										u1:=Difference(temp2,edge)[1];
										u3:=Difference(temp2,edge)[2];
						
										RemoveSet(temp3[1], Set([edge[1],u1,w]));
										RemoveSet(temp3[1], Set([edge[2],u1,w]));
										AddSet(temp3[1], Set([edge[1],edge[2],u1]));
										AddSet(temp3[1], Set([edge[1],edge[2],w]));

										RemoveSet(temp3[2], Set([edge[1],u1,w]));
										RemoveSet(temp3[2], Set([edge[2],u1,w]));
										AddSet(temp3[2], Set([edge[1],edge[2],u1]));
										AddSet(temp3[2], Set([edge[1],edge[2],w]));

										break;
									fi;
								od;
								
								InsertElement(eta,temp3[1],i+2);
								InsertElement(eta,temp3[2],i+3);
								
				 				#and don't forget about the orientation  HERE!
				 				
				 				InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
 								InsertElement(ori_eta,ori_check([eta[i+2],eta[i+3]],ori_eta[i+2]),i+3);
				 				
								
								temp_res:=temp_res+count_with_intersection([eta[i+1],eta[i+4]],Set([v1,k]),edge,ori_eta[i+1]);
								
								#MORE WORK HERE, only one cycle done from 3
								#now done
								
								
								temp:=[eta[i],eta[i+1]];
								temp2:=Set(Flat(link(temp[1], [j])));
								temp3:=ShallowCopy(temp);
								
								for edge in Combinations(temp2,2) do
									if not edge in eta[i] and not edge in eta[i+1] then
										# flip from edge
										u1:=Difference(temp2,edge)[1];
										u3:=Difference(temp2,edge)[2];
						
										RemoveSet(temp3[1], Set([edge[1],u1,j]));
										RemoveSet(temp3[1], Set([edge[2],u1,j]));
										AddSet(temp3[1], Set([edge[1],edge[2],u1]));
										AddSet(temp3[1], Set([edge[1],edge[2],j]));

										RemoveSet(temp3[2], Set([edge[1],u1,j]));
										RemoveSet(temp3[2], Set([edge[2],u1,j]));
										AddSet(temp3[2], Set([edge[1],edge[2],u1]));
										AddSet(temp3[2], Set([edge[1],edge[2],j]));

										break;
									fi;
								od;
								
								InsertElement(eta,temp3[1],i+1);
								InsertElement(eta,temp3[2],i+2);
								
				 				#and don't forget about the orientation  HERE!
				 				
				 				InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
 								InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
 								
 								temp_res:=temp_res+count_with_intersection([eta[i],eta[i+3]],Set([u,w]),edge,ori_eta[i]);

				 				######
				 				
				 				temp:=[eta[i+6],eta[i+7]];
								temp2:=Set(Flat(link(temp[1], [k])));
								temp3:=ShallowCopy(temp);
								
								for edge in Combinations(temp2,2) do
									if not edge in eta[i+6] and not edge in eta[i+7] then
										# flip from edge
										u1:=Difference(temp2,edge)[1];
										u3:=Difference(temp2,edge)[2];
						
										RemoveSet(temp3[1], Set([edge[1],u1,k]));
										RemoveSet(temp3[1], Set([edge[2],u1,k]));
										AddSet(temp3[1], Set([edge[1],edge[2],u1]));
										AddSet(temp3[1], Set([edge[1],edge[2],k]));

										RemoveSet(temp3[2], Set([edge[1],u1,k]));
										RemoveSet(temp3[2], Set([edge[2],u1,k]));
										AddSet(temp3[2], Set([edge[1],edge[2],u1]));
										AddSet(temp3[2], Set([edge[1],edge[2],k]));

										break;
									fi;
								od;
								
								InsertElement(eta,temp3[1],i+7);
								InsertElement(eta,temp3[2],i+8);
								
				 				#and don't forget about the orientation  HERE!
				 				
				 				InsertElement(ori_eta,ori_check([eta[i+6],eta[i+7]],ori_eta[i+6]),i+7);
 								InsertElement(ori_eta,ori_check([eta[i+7],eta[i+8]],ori_eta[i+7]),i+8);
				 				
								
								#count p,q,r				##TO DO
								
								temp_res:=temp_res+count_with_intersection([eta[i+6],eta[i+9]],Set([w1,w2]),edge,ori_eta[i+6]);
								
								Print("decomposition -> return ",temp_res,"\n");
								return temp_res;
							fi;
						od;
					fi;
				od;
			fi;
		od;
	fi;

	if (difficulty_eta[i] mod 6) = 4 then

		# The even-b setup needs L = eta[i] flanked by two moves, so eta[i-1] must
		# exist; at i = 1 there is no beta1 and the configuration is not present.

		if i > 1 and difficulty_eta[i]=2*difficulty_tri(eta[i]) then

			# L = eta[i] is the peak; beta1 takes it to eta[i-1] by flipping the
			# edge sigma1, beta2 to eta[i+1] by flipping sigma2.  L has minimum
			# degree 5, and one end of each sigma has degree exactly 5 -- the
			# paper calls those v1 and v2, and the other ends u1 and u2.

			deg_res:=degree(eta[i]);
			temp_faces:=[ve_count(eta[i-1]),ve_count(eta[i]),ve_count(eta[i+1])];

			sigma1:=fail;
			sigma2:=fail;

			for element in Combinations(U([eta[i-1],eta[i]]),2) do
				if element in temp_faces[2][2] and not element in temp_faces[1][2] then
					sigma1:=Set(element);
				fi;
			od;

			for element in Combinations(U([eta[i],eta[i+1]]),2) do
				if element in temp_faces[2][2] and not element in temp_faces[3][2] then
					sigma2:=Set(element);
				fi;
			od;

			if sigma1 = fail or sigma2 = fail then
				record_unhandled("b=4: could not identify sigma1/sigma2", i, eta, ori_eta, rec());
				continue;
			fi;

			if deg_res[sigma1[1]]=5 then v1:=sigma1[1]; u1:=sigma1[2];
			else                         v1:=sigma1[2]; u1:=sigma1[1]; fi;

			if deg_res[sigma2[1]]=5 then v2:=sigma2[1]; u2:=sigma2[2];
			else                         v2:=sigma2[2]; u2:=sigma2[1]; fi;

			# All three sub-cases of b = 4 have the same shape: choose an auxiliary
			# edge e such that gamma(L,sigma1,e) and gamma(L,sigma2,e) are both
			# defined, then replace
			#
			#     eta[i-1] <- eta[i] -> eta[i+1]        (peak complexity)
			#
			# by the four moves
			#
			#     eta[i-1] -> flip_e(eta[i-1]) -> flip_e(eta[i]) -> flip_e(eta[i+1]) -> eta[i+1]
			#
			# which routes around the peak: the outer two are the e-flip and its
			# inverse, and the inner two are beta1 and beta2 carried across it.
			# Only the choice of e, and the sign, differ between the sub-cases.
			#
			# The paper's last case is when v1 and v2 are joined by an edge, so
			# their degrees do not drop to 4 along the generic chain.  It splits
			# on whether L already contains the edge u1u2 of its figure, because
			# the flip of v1w -- the one the "absent" half needs -- is exactly the
			# flip that would create u1u2.
			#
			#     figure   sigma1  sigma2  v1  v2  u1  u2  w   u1u2
			#     here     sigma1  sigma2  v1  v2  w1  u2  w4  [w1,u2]

			temp2:=[];
			case:='g';

			if Set([v1,v2]) in temp_faces[2][2] then

				w1:=Difference(Set(Flat(link(eta[i],sigma1))),[v2]);
				w4:=Difference(Set(Flat(link(eta[i],Set([u2,v1])))),[v2]);

				if Length(w1)=1 and Length(w4)=1 then
					if Set([w1[1],u2]) in temp_faces[2][2] then
						Add(temp2, Set([w1[1],u2]));       # last case, u1u2 present
						case:='p';
					else
						Add(temp2, Set([v1,w4[1]]));       # last case, u1u2 absent
						case:='a';
					fi;
				fi;

			fi;

			# Generic choice: an edge at a degree-5 vertex taking no part in either
			# move.  L has at least 12 vertices of degree 5 and at most 8 of them
			# participate, so such a vertex exists; at least three of its five
			# edges carry a defined move.

			temp:=U([eta[i-1],eta[i]]);
			UniteSet(temp,U([eta[i],eta[i+1]]));

			for w in [1..Length(deg_res)] do
				if deg_res[w]=5 and not w in temp then
					for vertex in Set(Flat(link(eta[i],[w]))) do
						Add(temp2, Set([w,vertex]));
					od;
				fi;
			od;

			# gamma(L,sigma,e) is defined when the flips of sigma and e commute.
			# Following the definition of gamma that needs two things: the flip of
			# e must be available in eta[i-1] and eta[i+1] as well as in eta[i],
			# and no simplex of L may contain both e and sigma -- if e shares a
			# triangle with sigma, flipping e changes the link of sigma and the
			# two orders of flipping give different spheres.  Take the first
			# candidate that qualifies; the prescribed last-case edge is first in
			# the list when it applies.

			temp1:=fail;

			for edge in temp2 do
				if flip_defined(eta[i-1],edge) and flip_defined(eta[i],edge)
				   and flip_defined(eta[i+1],edge)
				   and not ForAny(eta[i], t -> IsSubsetSet(t,edge) and IsSubsetSet(t,sigma1))
				   and not ForAny(eta[i], t -> IsSubsetSet(t,edge) and IsSubsetSet(t,sigma2)) then
					temp1:=edge;
					break;
				fi;
			od;

			if temp1 = fail then
				record_unhandled("b=4: no auxiliary edge with both gammas defined",
				                 i, eta, ori_eta,
				                 rec( sigma1:=sigma1, sigma2:=sigma2, candidates:=temp2 ));
				continue;
			fi;

			if Length(temp2) = 0 or temp1 <> temp2[1] then
				case:='g';
			fi;

			# count_with_intersection takes bis_edge as an edge of bis[1]; for the
			# pair [eta[i-1],eta[i]] that is eta[i-1], where beta1 has already
			# replaced sigma1 by its link.

			temp_res:=count_with_intersection([eta[i-1],eta[i]],Set(Flat(link(eta[i],sigma1))),temp1,ori_eta[i-1])
			         +count_with_intersection([eta[i],eta[i+1]],sigma2,temp1,ori_eta[i]);

			# The generic chain and the u1u2-absent half both read
			# -gamma(.,sigma1,.) + gamma(.,sigma2,.), which is the sum above; the
			# u1u2-present half carries the opposite pattern.

			if case='p' then
				temp_res:=-temp_res;
			fi;

			temp3:=flip_edge(eta[i-1],temp1);
			temp4:=flip_edge(eta[i],temp1);
			temp5:=flip_edge(eta[i+1],temp1);

			eta[i]:=temp3;
			InsertElement(eta,temp4,i+1);
			InsertElement(eta,temp5,i+2);

			ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
			InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
			InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);

			if case='p' then
				Print("b=4 -> last case, edge u1u2 present\n");
			elif case='a' then
				Print("b=4 -> last case, edge u1u2 absent\n");
			else
				Print("b=4 -> generic\n");
			fi;
			Print("decomposition -> return ",temp_res,"\n");
			return temp_res;

		fi;
	fi;

	if (difficulty_eta[i] mod 6) = 5 then
		deg_f:=degree(eta[i]);
		deg_res:=degree(eta[i+1]);
		
		Print("b=5\n");
		
		for k in [1..Length(deg_f)] do
			if (deg_f[k]=5) and not (k in U([eta[i],eta[i+1]])) then
				temp:=eta[i];
				temp2:=Set(Flat(link(temp[1],[k])));
				temp3:=ShallowCopy([eta[i],eta[i+1]]);
				
				temp_faces:=[];				
				temp_faces[1]:=ve_count(eta[i]);
				temp_faces[2]:=ve_count(eta[i+1]);
				
				
				for j in [1..5] do
					for l in [1..5] do
						if j<>l and not Set([temp2[j],temp2[l]]) in temp_faces[1][2] and not Set([temp2[j],temp2[l]]) in temp_faces[2][2] then
							temp1:=Set(Intersection(link(link(eta[i],[k]),[temp2[j]]),link(link(eta[i],[k]),[temp2[l]])));
							AddSet(temp1, temp2[j]);
							RemoveSet(temp3[1], temp1);
							RemoveSet(temp3[2], temp1);
							RemoveSet(temp1, temp2[j]);
							AddSet(temp1, temp2[l]);
							RemoveSet(temp3[1], temp1);
							RemoveSet(temp3[2], temp1);
							RemoveSet(temp1, k);
							AddSet(temp1, temp2[j]);
							AddSet(temp3[1], temp1);
							AddSet(temp3[2], temp1);
							AddSet(temp3[1], Set([k,temp2[j],temp2[l]]));
							AddSet(temp3[2], Set([k,temp2[j],temp2[l]]));
							
							#change eta
							
							InsertElement(eta,temp3[1],i+1);
							InsertElement(eta,temp3[2],i+2);
							
							#ori_eta
							
							InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
							InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
							
							#p,q,r
							#variables reused! temp
							#temp2 used
							
							temp_ori:=ori_spread(eta[i],ori_eta[i]);
							
							v:=IntersectionSet(Set(Flat(link(eta[i],Set([temp2[j],k])))),Set(Flat(link(eta[i],Set([temp2[l],k])))));
							RemoveSet(v,k);
							v:=v[1];
							
							if simp_ori(eta[i],temp_ori,[temp2[j],k,v])=1 then
								v1:=temp2[j];
								v2:=temp2[k];
							else
								v1:=temp2[k];
								v2:=temp2[j];
							fi;
							
							temp:=IntersectionSet(Set([v,v1,v2]),U([eta[i+1],eta[i+2]]));
							
							if Length(temp)=0 then
								Print("decomposition -> return ",0,"\n");
								return 0;
							elif temp=[v1] then
								if deg_f[v1]<deg_res[v1] then
									temp4:=IntersectionSet(Set(Flat(link(eta[i], [v1]))), U([eta[i+1],eta[i+2]]));
									if simp_ori(eta[i],temp_ori,[temp4[1],temp4[2],v1])=1 then
										w1:=temp4[1];
										w2:=temp4[2];
									else
										w1:=temp4[2];
										w2:=temp4[1];
									fi;
									
									temp_res:=count_ro(count_pq(eta[i],w1,w2,v,k,v1));
									Print("decomposition -> return ",temp_res,"\n");
									return temp_res;
								else
									w3:=Difference(Difference(U([eta[i],eta[i+1]]),Set(Flat(link(eta[i],[v1])))),[v1]);
									temp4:=IntersectionSet(Set(Flat(link(eta[i+3], [v1]))), U([eta[i+1],eta[i+2]]));
									if simp_ori(eta[i],temp_ori,[w3,v1,temp4[1]])=1 then
										w1:=temp4[1];
										w2:=temp4[2];
									else
										w1:=temp4[2];
										w2:=temp4[1];
									fi;
									
									temp_res:=-count_ro(count_pq(eta[i],w1,w2,v,k,v1));
									Print("decomposition -> return ",temp_res,"\n");
									return temp_res;
								fi;
							elif temp=[v] then
								if deg_f[v]<deg_res[v] then
									temp4:=IntersectionSet(Set(Flat(link(eta[i], [v]))), U([eta[i+1],eta[i+2]]));
									if simp_ori(eta[i],temp_ori,[temp4[1],temp4[2],v])=1 then
										w1:=temp4[1];
										w2:=temp4[2];
									else
										w1:=temp4[2];
										w2:=temp4[1];
									fi;
									
									temp_res:=-count_ro(count_pq(eta[i],w1,w2,v2,v1,v));
									Print("decomposition -> return ",temp_res,"\n");
									return temp_res;
								else
									w3:=Difference(Difference(U([eta[i],eta[i+1]]),Set(Flat(link(eta[i],[v])))),[v]);
									temp4:=IntersectionSet(Set(Flat(link(eta[i+3], [v]))), U([eta[i+1],eta[i+2]]));
									if simp_ori(eta[i],temp_ori,[w3,v,temp4[1]])=1 then
										w1:=temp4[1];
										w2:=temp4[2];
									else
										w1:=temp4[2];
										w2:=temp4[1];
									fi;
									
									temp_res:=count_ro(count_pq(eta[i],w1,w2,v2,v1,v));
									Print("decomposition -> return ",temp_res,"\n");
									return temp_res;
								fi;
							elif temp=[v2] then
								if deg_f[v2]<deg_res[v2] then
									temp4:=IntersectionSet(Set(Flat(link(eta[i], [v2]))), U([eta[i+1],eta[i+2]]));
									if simp_ori(eta[i],temp_ori,[temp4[1],temp4[2],v2])=1 then
										w1:=temp4[1];
										w2:=temp4[2];
									else
										w1:=temp4[2];
										w2:=temp4[1];
									fi;
									
									temp_res:=count_ro(count_pq(eta[i],w1,w2,k,v,v2));
									Print("decomposition -> return ",temp_res,"\n");
									return temp_res;
								else
									w3:=Difference(Difference(U([eta[i],eta[i+1]]),Set(Flat(link(eta[i],[v2])))),[v2]);
									temp4:=IntersectionSet(Set(Flat(link(eta[i+3], [v2]))), U([eta[i+1],eta[i+2]]));
									if simp_ori(eta[i],temp_ori,[w3,v2,temp4[1]])=1 then
										w1:=temp4[1];
										w2:=temp4[2];
									else
										w1:=temp4[2];
										w2:=temp4[1];
									fi;
									
									temp_res:=-count_ro(count_pq(eta[i],w1,w2,k,v,v2));
									Print("decomposition -> return ",temp_res,"\n");
									return temp_res;
								fi;
							elif temp=Set([v1,v]) then
								if deg_f[v]<deg_res[v] then
									temp_res:=count_ro([0,Length(link(eta[i],[v]))-3])-count_ro([0,Length(link(eta[i],[v1]))-3]);
									Print("decomposition -> return ",temp_res,"\n");
									return temp_res;
								else
									temp_res:=-count_ro([0,Length(link(eta[i],[v]))-4])+count_ro([0,Length(link(eta[i],[v1]))-2]);
									Print("decomposition -> return ",temp_res,"\n");
									return temp_res;
								fi;
							elif temp=Set([v,v2]) then
								if deg_f[v]<deg_res[v] then
									temp_res:=count_ro([0,Length(link(eta[i],[v2]))-3])-count_ro([0,Length(link(eta[i],[v]))-3]);
									Print("decomposition -> return ",temp_res,"\n");
									return temp_res;
								else
									temp_res:=-count_ro([0,Length(link(eta[i],[v2]))-4])+count_ro([0,Length(link(eta[i],[v]))-2]);
									Print("decomposition -> return ",temp_res,"\n");
									return temp_res;
								fi;
								
							fi;
						fi;
					od;
				od;
			fi;
		od;
	fi;

	if (difficulty_eta[i] mod 6) = 0 then
		temp1:=[];
		temp2:=[];
		temp3:=[];
		
		if difficulty_eta[i]=2*difficulty_tri(eta[i]) then
				
			temp1:=Difference(Set(Flat(eta[i])), Flat(eta[i-1]))[1];
			temp2:=Difference(Set(Flat(eta[i])), Flat(eta[i+1]))[1];
			temp3:=IntersectionSet(U([eta[i],eta[i+1]]),U([eta[i-1],eta[i]]));
			temp4:=Set(Flat(link(eta[i],[temp1])));
			temp5:=Set(Flat(link(eta[i],[temp2])));
			
			RemoveSet(eta[i], Set([temp1,temp4[1],temp4[2]]));
			RemoveSet(eta[i], Set([temp1,temp4[1],temp4[3]]));
			RemoveSet(eta[i], Set([temp1,temp4[2],temp4[3]]));
			RemoveSet(eta[i], Set([temp2,temp5[1],temp5[2]]));
			RemoveSet(eta[i], Set([temp2,temp5[1],temp5[3]]));
			RemoveSet(eta[i], Set([temp2,temp5[2],temp5[3]]));
				
			AddSet(eta[i], Set(temp4));
			AddSet(eta[i], Set(temp5));
			
			ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
			
			Print("b=6 - Intersection of U - ", temp3, "\n");
								
			if temp3=[] then
				
				Print("decomposition -> return ",0,"\n");
				return 0;
				
			elif Length(temp3)=1 then
								
				# with p and q
				
				temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
				u:=temp3[1];
				
				RemoveSet(temp4,u);
				RemoveSet(temp5,u);
				
				if simp_ori(eta[i],temp_ori,[u,temp4[2],temp4[1]])=1 then
					v1:=temp4[1];
					v2:=temp4[2];
				else
					v1:=temp4[2];
					v2:=temp4[1];
				fi;
				
				if simp_ori(eta[i],temp_ori,[u,temp5[1],temp5[2]])=1 then
					w1:=temp5[1];
					w2:=temp5[2];
				else
					w1:=temp5[2];
					w2:=temp5[1];
				fi;
				
				Print("  ->intersection - 1 vertex - u=",u,"\n");
				
				temp_res:=-count_ro(count_pq(eta[i],v2,v1,w2,w1,u));
				Print("decomposition -> return ",temp_res,"\n");
				return temp_res;
				
			elif Length(temp3)=2 then
				
				# with p and q
				
				temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
				v:=Difference(temp4,temp3)[1];
				
				if simp_ori(eta[i],temp_ori,[v,temp3[1],temp3[2]])=1 then
					u1:=temp3[1];
					u2:=temp3[2];
				else
					u1:=temp3[2];
					u2:=temp3[1];
				fi;
						
				Print("  ->intersection - 2 vertices - u1=",u1,", u2=",u2,"\n");
				
				
				temp_res:=-count_ro([0,Length(link(eta[i],[u1]))-2])+count_ro([0,Length(link(eta[i],[u2]))-2]);
				Print("decomposition -> return ",temp_res,"\n");
				return temp_res;
				
			fi;
		fi;		
	fi;
od;

# Reaching this point means no position of max_pos produced a value: every
# position either failed the "eta[i] is the peak" guard or hit a configuration
# outside its case chain.  Returning nothing here surfaces in Gamma2.g as
# "must return a value" with none of the state that explains it, so stop here
# instead, while eta, ori_eta and unhandled_cases are still inspectable.

Error("decomposition: no case matched at any position of max_pos ", max_pos,
      " (max difficulty ", Maximum(difficulty_eta),
      ", difficulty mod 6 = ", Maximum(difficulty_eta) mod 6,
      "); ", Length(unhandled_cases), " configuration(s) recorded in unhandled_cases");

end;
