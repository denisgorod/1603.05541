##### Compile the file Gamma2.g, not this one #####

####### Some variables ##########

################################### General functions #####################################


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

ReverseList:=function(list)

	local new_list, i;
	new_list:=[];
	
	for i in [1..Length(list)] do
		new_list[i]:=list[Length(list)+1-i];
	od;
		
	return new_list;

end;

##

link:=function(mfd,simplex)

	local  i,j,facetsmut;

	facetsmut:=[];;

	for i in [1 .. Length(mfd)] do
		Add(facetsmut, []);;
		for j in [1 .. Length(mfd[1])] do
			AddSet(facetsmut[i],mfd[i][j]);;
		od;

		if IsSubsetSet(mfd[i], simplex) = true then
			SubtractSet(facetsmut[i], simplex);;
		else 
			facetsmut[i]:=0;					
		fi;
	od;

	for i in [0 .. Length(mfd)-1] do	

		if facetsmut[Length(mfd)-i]=0 then
			Remove(facetsmut,Length(mfd)-i);;
		fi;

	od;

	return Set(facetsmut);	

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
	local result, simplex, link_b, link_f, i;
	result:=[];
	
	for i in Set(Concatenation(Flat(bis[1]),Flat(bis[2]))) do
		if Set(link(bis[1],[i]))<>Set(link(bis[2],[i])) then
			Add(result, i);
		fi;
	od;
	
	#Print("U: processed \n");
	return Set(result);
end;

##
print_U_eta:=function(eta)

	local b;
	for b in [1 .. Length(eta)-1] do
		Print(b," ",U([eta[b],eta[b+1]]),"\n");
	od;

end;

##
degree:=function(L)

	local degr, vertices, edge, edges, vertex;
	
	degr:=[];

	vertices:=ve_count(L)[1];
	edges:=ve_count(L)[2];
	degr:=ListWithIdenticalEntries(Maximum(Flat(vertices)),0);
	
	for vertex in vertices do
		degr[vertex[1]]:=0;
		for edge in edges do
			if IsSubset(edge,vertex) then
				degr[vertex[1]]:=degr[vertex[1]]+1;
			fi;
		od;
	od;
	
	#Print("degree: Degree of", L, "computed - ", degr, "\n");
	return degr;

end;

duplicate_free_eta:=function(eta,ori_eta)
	local b,c;
	for c in [1 .. Length(eta)-2] do
		for b in [1 .. Length(eta)-2] do
			if Length(eta)>b+1 and U([eta[b],eta[b+1]])=U([eta[b+1],eta[b+2]]) then
				Remove(eta,b);
				Remove(eta,b);
				Remove(ori_eta,b);
				Remove(ori_eta,b);
			fi;
		od;
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

	local ori2n, j, vertex, vertemp, newface;
	
	for j in [1..Length(bis[2])] do
		if bis[1][ori1[1]]=bis[2][j] then
			#Print("ori_check -> easy case\n");
			return [j,ori1[2]];
		fi;
	od;
	
	
	for vertex in bis[1][ori1[1]] do
		if vertex in U(bis) then
			for vertemp in Set(Flat(bis[1])) do
				newface:=ShallowCopy(bis[1][ori1[1]]);
				RemoveSet(newface,vertex);
				AddSet(newface,vertemp);
				if newface in bis[2] and not IsSubset(U(bis), newface) then
					ori2n:=((( Position( bis[1][ori1[1]], Difference(bis[1][ori1[1]], newface)[1]) - Position(newface , Difference(newface,bis[1][ori1[1]])[1]) ) mod 2) * 2) - 1;
					#Print("ori_check -> hard case\n");
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

	local i, j, graph, bool, simplex, edges, vertices, covertices, covertex, faces, edge, vertex, temp, simp, dir, bool2, temp_ori, beg_pos;
	bool:=[];
	bool2:=[];
	graph:=[];
	edges:=[];
	temp_ori:=[];
	vertices:=[];
	
	faces:=faces_count(L);
	vertices:=faces[1];
	covertices:=faces[Length(faces_count(L))-1];
	
	for covertex in covertices do
		temp:=[];
		for vertex in vertices do
			simp:=Set(Concatenation(vertex,covertex));
			if Length(simp)=Length(L[1]) and simp in L then
				AddSet(temp, Position(L, simp));
			fi;
		od;
		Add(graph, temp);
	od;

	beg_pos:=ori[1];
	temp_ori[beg_pos]:=ori[2];
	bool:=ListWithIdenticalEntries(Length(L),false);
	bool2:=ListWithIdenticalEntries(Length(L),false);
	
	ori_step(L, beg_pos, temp_ori, bool, graph);
	bool2[beg_pos]:=true;
	
	for i in [1..Length(L)] do
		for j in [1..Length(L)] do
			if bool2[j]=false and bool[j]=true then
				#Print("Inside ori_spread\n");
				ori_step(L, j , temp_ori, bool, graph);
				bool2[j]:=true;
			fi;
		od;
	od;

return temp_ori;

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

	local k, number, deg, edges, vertices, edge, vertex, element;
	deg:=[];
	vertices:=[];
	edges:=[];

	for k in [1..2] do

	        faces[k]:=[];
	        for element in L do
			if Length(element) >= k then
				UniteSet(faces[k],Combinations(element,k));
			fi;
	        od;
	od;

	vertices:=faces[1];
	edges:=faces[2];

	for vertex in vertices do
		deg[vertex[1]]:=0;
		for edge in edges do
			if IsSubset(edge,vertex) then
				deg[vertex[1]]:=deg[vertex[1]]+1;
			fi;
		od;
	od;

	for number in deg do
		if number=3 then 
			return 3*Length(faces[1]);
		fi;
	od;

	for number in deg do
		if number=4 then 
			return 3*Length(faces[1])+1;
		fi;
	od;

	return 3*Length(faces[1])+2;

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
	
	if debug > 2 then
		Print("  count_pq: ->cycle:", cycle, "\n");
	fi;
	
	Remove(cycle);
	
	if (Position(cycle,ru)>Position(cycle,rd) and Position(cycle,ld)>Position(cycle,lu)) or (Position(cycle,lu)>Position(cycle,ru) and Position(cycle,rd)>Position(cycle,ld)) then
		p:=(Position(cycle,lu)-Position(cycle,ru)) mod Length(cycle);
		q:=(Position(cycle,rd)-Position(cycle,ld)) mod Length(cycle);
	else
		p:=(Position(cycle,ru)-Position(cycle,lu)) mod Length(cycle);
		q:=(Position(cycle,ld)-Position(cycle,rd)) mod Length(cycle);
	fi;
	
	if debug > 2 then
		Print("  count_pq: ->p=",p,", q=",q,"\n");
	fi;
	
	return [p,q];	

end;

##
count_ro:=function(pq)

	local p,q;
	p:=pq[1];
	q:=pq[2];

	if debug > 2 then
		Print("  count_ro: ->p=",p,", q=",q,", ",(q-p)/((p+q+2)*(p+q+3)*(p+q+4))," returned\n");
	fi;
	
	return (q-p)/((p+q+2)*(p+q+3)*(p+q+4));

end;

##
count_omega:=function(p)

	if debug > 2 then
		Print("  count_omega: ->p=",p,", ",1/((p+2)*(p+3))," returned\n");
	fi;
	return 1/((p+2)*(p+3));
	
end;


### Special for b=3 ###

count_value_ghi:=function(bis,bis_edge,edge,ori1)

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
				return count_ro(count_pq(bis[1],link_bis_edge[2],link_bis_edge[1],edge[2],edge[1]));
			elif simp_ori(bis[1],temp_ori1,[v,link_bis_edge[1],w])=1 then
				return count_ro(count_pq(bis[1],link_bis_edge[2],link_bis_edge[1],edge[1],edge[2]));
			elif simp_ori(bis[1],temp_ori1,[v,edge[1],edge[2]])=1 then
				return count_ro(count_pq(bis[1],link_bis_edge[1],link_bis_edge[2],edge[2],edge[1]));
			elif simp_ori(bis[1],temp_ori1,[v,link_bis_edge[1],w])=-1 and simp_ori(bis[1],temp_ori1,[v,edge[1],edge[2]])=-1 then
				return count_ro(count_pq(bis[1],link_bis_edge[1],link_bis_edge[2],edge[1],edge[2]));
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
			u:=Difference(edge, w)[1];
			temp:=simp_ori(bis[1],temp_ori1,[w,v,u]);
			return -temp * (count_ro([0,Length(link(bis[1],[w]))-3])-count_ro([0,Length(link(bis[1],[v]))-3]));
		elif w in edge then
			u:=Difference(edge, w)[1];
			temp:=simp_ori(bis[1],temp_ori1,[w,v,u]);
			return temp * (count_ro([0,Length(link(bis[1],[w]))-4])-count_ro([0,Length(link(bis[1],[v]))-2]));
		elif v in bis_edge then
			u:=Difference(edge, v)[1];
			temp:=simp_ori(bis[1],temp_ori1,[w,v,u]);
			return -temp * (count_ro([0,Length(link(bis[1],[w]))-2])-count_ro([0,Length(link(bis[1],[v]))-4]));
		elif w in bis_edge and v in edge then
			u:=Difference(edge, v)[1];
			temp:=simp_ori(bis[1],temp_ori1,[w,v,u]);
			return temp * (count_ro([0,Length(link(bis[1],[w]))-3])-count_ro([0,Length(link(bis[1],[v]))-3]));
		fi;
	fi;
	
	Print("ERROR! THIS SHOULD NEVER HAPPEN!");
	return 0;

end;

#count_value_abc:=function(bis,bis_simplex,simplex,ori1)
#
#	local U1, U2, intersection, link_simplex, link_bis_edge, temp_ori1, v, w, u, temp;
#	
#end;


######################################## Decomposition #################################################


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
				
				if debug > 1 then
					Print("b=1 -> case deg 3, vertex ", j,"\n");
				fi;
				
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
					if debug > 0 then
						Print("decomposition -> return ",0,"\n");
					fi;
					return 0;
				elif Length(u)=1 then
					
					# д
					
					# not so great
					
					if debug > 1 then
						Print("  ->intersection - 1 vertex - ",u[1],"\n");
					fi;
					
					u:=u[1];
					
					if deg_f[u]<deg_res[u] then
					
						temp_ori:=ori_spread(eta[i],ori_eta[i]);
					
						temp:=Set(Flat(link(eta[i],Set([u,j]))));
						temp2:=IntersectionSet(U([eta[i+1],eta[i+2]]),Set(Flat(link(eta[i+1],[u]))));
						if simp_ori(eta[i],temp_ori,[j,u,temp[1]]) = 1 then
							if simp_ori(eta[i],temp_ori,[u,temp2[2],temp2[1]])=1 then
								temp_res:=count_ro(count_pq(eta[i],temp[1],temp[2],temp2[1],temp2[2],u));
								if debug > 0 then
									Print("decomposition -> return ",temp_res,"\n");
								fi;
								return temp_res;
							else
								temp_res:=count_ro(count_pq(eta[i],temp[1],temp[2],temp2[2],temp2[1],u));
								if debug > 0 then
									Print("decomposition -> return ",temp_res,"\n");
								fi;
								return temp_res;
							fi;
						else
							if simp_ori(eta[i],temp_ori,[u,temp2[2],temp2[1]])=1 then
								temp_res:=count_ro(count_pq(eta[i],temp[2],temp[1],temp2[1],temp2[2],u));
								if debug > 0 then
									Print("decomposition -> return ",temp_res,"\n");
								fi;
								return temp_res;
							else
								temp_res:=count_ro(count_pq(eta[i],temp[2],temp[1],temp2[2],temp2[1],u));
								if debug > 0 then
									Print("decomposition -> return ",temp_res,"\n");
								fi;
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
								if debug > 0 then
									Print("decomposition -> return ",temp_res,"\n");
								fi;
								return temp_res;
							else
								temp_res:=-count_ro(count_pq(eta[i],temp[1],temp[2],temp2[2],temp2[1],u));
								if debug > 0 then
									Print("decomposition -> return ",temp_res,"\n");
								fi;
								return temp_res;
							fi;
						else
							if simp_ori(eta[i+3],temp_ori,[u,temp2[2],temp2[1]])=1 then
								temp_res:=-count_ro(count_pq(eta[i],temp[2],temp[1],temp2[1],temp2[2],u));
								if debug > 0 then
									Print("decomposition -> return ",temp_res,"\n");
								fi;
								return temp_res;
							else
								temp_res:=-count_ro(count_pq(eta[i],temp[2],temp[1],temp2[2],temp2[1],u));
								if debug > 0 then
									Print("decomposition -> return ",temp_res,"\n");
								fi;
								return temp_res;
							fi;
						fi;
						
						## RETURN RO
					fi;
										
				else
					# Length(u)=2, a bit better
					if debug > 1 then
						Print("  ->intersection - 2 vertices - ",u[1],", ",u[2],"\n");
					fi;
					
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
						if debug > 0 then
							Print("decomposition -> return ",temp_res,"\n");
						fi;
						return temp_res;
					else
						# -e
						temp_res:=-count_ro([0,Length(link(eta[i],[u1]))-4])-count_ro([0,Length(link(eta[i],[u2]))-3]);
						if debug > 0 then
							Print("decomposition -> return ",temp_res,"\n");
						fi;
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
						
						if debug > 1 then
							Print("b=1 -> case deg 3-4, vertices ", j,", ", k, "\n");
						fi;
						
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
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
							return temp_res;
							
						else 
							tempp:=Difference(Set(Flat(link(eta[i],[j]))),Set([v,k]))[1];
							tempr:=Difference(Set(Flat(link(eta[i],[k]))),Set([tempp,v,j]))[1];

							p:=degree(eta[i+1])[tempp] - 2;
							q:=degree(eta[i+1])[v] - 2;
							r:=degree(eta[i+1])[tempr] - 2;
							
							temp_res:=count_omega(p)-count_omega(q)+count_omega(r)- 1/12;
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
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
							if debug > 1 then
								Print("b=2 -> a\n");
							fi;
						else
							#b2
							case:='2';
							if debug > 1 then
								Print("b=2 -> b2\n");
							fi;
						fi;
					else
						#b1a
						if Length(IntersectionSet(Flat(link(eta[i],sigma2)), sigma1)) = 0 then
							#b1
							case:='1';
							if debug > 1 then
								Print("b=2 -> b1\n");
							fi;
						else
							#e
							case:='e';
							if debug > 1 then
								Print("b=2 -> e\n");
							fi;
						fi;
					fi;
					
				elif Length(IntersectionSet(link(eta[i],sigma1), link(eta[i],sigma2))) = 1 then
					#c
					case:='c';
					if debug > 1 then
						Print("b=2 -> c\n");
					fi;
				else
					#i
					case:='i';
					if debug > 1 then
						Print("b=2 -> i\n");
					fi;
				fi;
			else
				#dfghjk
				if Length(IntersectionSet(link(eta[i],sigma1), link(eta[i],sigma2))) = 0 then
					#dgh
					if Length(IntersectionSet(Flat(link(eta[i],sigma1)), sigma2)) = 0 then
						#d
						case:='d';
						if debug > 1 then
							Print("b=2 -> d\n");
						fi;
					else
						#gh
						if degree(eta[i])[IntersectionSet(sigma1,sigma2)[1]] > 4 then
							#g
							case:='g';
							if debug > 1 then
								Print("b=2 -> g\n");
							fi;
						else
							#h
							case:='h';
							if debug > 1 then
								Print("b=2 -> h\n");
							fi;
						fi;
					fi;
				elif Length(IntersectionSet(link(eta[i],sigma1), link(eta[i],sigma2))) = 1 then
					#f
					case:='f';
					if debug > 1 then
						Print("b=2 -> f\n");
					fi;
				else
					#jk
					if Set(Union(Difference(sigma1,sigma2),Difference(sigma2,sigma1))) in tempve[2][2] then
						#k
						case:='k';
						if debug > 1 then
							Print("b=2 -> k\n");
						fi;
					else
						#j
						case:='j';
						if debug > 1 then
							Print("b=2 -> j\n");
						fi;
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
				
				if debug > 0 then
					Print("decomposition -> return ",0,"\n");
				fi;
				
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
				
				if debug > 0 then
					Print("decomposition -> return ",temp_res,"\n");
				fi;
				
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
				
				if debug > 0 then
					Print("decomposition -> return ",temp_res,"\n");
				fi;
				
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
				
				if debug > 0 then
					Print("decomposition -> return ",temp_res,"\n");
				fi;
				
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
				
				if debug > 0 then
					Print("decomposition -> return ",temp_res,"\n");
				fi;
				
				return temp_res;
				
			elif case='e' then
				
				#      	          __ __
				# side touching  | /| /|
				#   		 |/_|/_|
				
				# p,q,r
				
				v1:=IntersectionSet(sigma1,U([eta[i],eta[i+1]]))[1];
				v2:=IntersectionSet(sigma2,U([eta[i-1],eta[i]]))[1];
				
				if Length(link(eta[i],[v1]))=4 and Length(link(eta[i],[v2]))=4 then
				
					if debug > 1 then
						Print("  ->special case\n");
					fi;
									
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
					
					if debug > 0 then
						Print("decomposition -> return ",temp_res,"\n");
					fi;
					
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
					
					if debug > 0 then
						Print("decomposition -> return ",temp_res,"\n");
					fi;
					
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
				
				if debug > 0 then
					Print("decomposition -> return ",temp_res,"\n");
				fi;
				
				return temp_res;
				
			elif case='g' then
			
				#	________
				#	\  /\  /
				#	 \/__\/
				
				# two subcases here
				
				u:=Intersection(sigma1,sigma2)[1];
				v1:=Difference(sigma1,[u])[1];
				v2:=Difference(sigma2,[u])[1];
				w1:=Difference(Set(Flat(link(eta[i],Set([v1,v2])))),[u])[1];
				w2:=Difference(Set(Flat(link(eta[i],sigma1))),[v2])[1];
				w3:=Difference(Set(Flat(link(eta[i],sigma2))),[v1])[1];
				
				if not Set([u,w1]) in tempve[2][2] then
					
					# easy case
					
					if debug > 1 then
						Print("  ->easy case - u=",u,", v1=",v1,", v2=",v2,"\n");
					fi;
					
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
					
					if debug > 0 then
						Print("decomposition -> return ",temp_res,"\n");
					fi;
					
					return temp_res;
				
				else								
					#hard one
					
					if debug > 1 then
						Print("  ->hard case\n");
					fi;
					
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
					if debug > 0 then
						Print("decomposition -> return ",temp_res,"\n");
					fi;
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
				if debug > 0 then
					Print("decomposition -> return ",temp_res,"\n");
				fi;
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
					if debug > 1 then
						Print("  ->w3=v2\n");
					fi;
					temp_res:=temp_res - count_ro([0,Length(link(eta[i-1],[w1]))-4]) + count_ro([0,1]);
					if debug > 0 then
						Print("decomposition -> return ",temp_res,"\n");
					fi;
					return temp_res;
				else
					temp_res:=temp_res + count_ro(count_pq(eta[i+2],u1,w3,u2,v2,w1));
					if debug > 0 then
						Print("decomposition -> return ",temp_res,"\n");
					fi;
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
				if debug > 0 then
					Print("decomposition -> return ",temp_res,"\n");
				fi;
				return temp_res;
				
			elif case='k' then
			
				
				v:=IntersectionSet(sigma1,sigma2)[1];
				u1:=Set(Union(Difference(sigma1,sigma2),Difference(sigma2,sigma1)))[1];
				u2:=Set(Union(Difference(sigma1,sigma2),Difference(sigma2,sigma1)))[2];
				
				# p,q,r + spreading orientation
				
				temp_ori:=ori_spread(eta[i],ori_eta[i]);
				
				if simp_ori(eta[i],temp_ori,[link(eta[i],Set([u1,u2]))[1],u1,u2])=1 then
					w3:=Set(Flat(link(eta[i],Set([u1,u2]))))[1];
					w4:=Set(Flat(link(eta[i],Set([u1,u2]))))[2];
				else
					w3:=Set(Flat(link(eta[i],Set([u1,u2]))))[2];
					w4:=Set(Flat(link(eta[i],Set([u1,u2]))))[1];
				fi;
				
				if simp_ori(eta[i],temp_ori,[link(eta[i],Set([u1,v]))[1],u1,v])=1 then
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
				if debug > 0 then
					Print("decomposition -> return ",temp_res,"\n");
				fi;
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
				
				if debug > 1 then
					Print("b=3 -> deg 4, j=",j,"\n");
				fi;
				
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
				
					if debug > 0 then
						Print("decomposition -> return ",0,"\n");
					fi;
					
					return 0;
				
				elif temp=[v1] then
				
					if debug > 1 then
						Print("  ->intersection - v1\n");
 					fi;
 				
					if deg_f[v1]<deg_res[v1] then
						temp2:=IntersectionSet(Set(Flat(link(eta[i],[v1]))),U([eta[i+1],eta[i+2]]));
						if simp_ori(eta[i+1],temp_ori,[temp2[1],v1,temp2[2]])=1 then
							#COUNT->RETURN
							temp_res:=count_ro(count_pq(eta[i],temp2[2],temp2[1],j,u1,v1));
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
							return temp_res;
						else
							#COUNT->RETURN
							temp_res:=count_ro(count_pq(eta[i],temp2[1],temp2[2],j,u1,v1));
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
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
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
							return temp_res;
						else
							#COUNT->RETURN
							temp_res:=-count_ro(count_pq(eta[i],temp2[2],temp2[1],j,u1,v1));
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
							return temp_res;
						fi;										
					fi;
				
 				elif temp=[u1] then
 				
 					if debug > 1 then
 						Print("  ->intersection - u1\n");
 					fi;
 				
 					if deg_f[u1]<deg_res[u1] then
						temp2:=IntersectionSet(Set(Flat(link(eta[i],[u1]))),U([eta[i+1],eta[i+2]]));
						if simp_ori(eta[i+1],temp_ori,[temp2[1],u1,temp2[2]])=1 then
							#COUNT->RETURN
							temp_res:=-count_ro(count_pq(eta[i],temp2[2],temp2[1],v1,v2,u1));
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
							return temp_res;
						else
							#COUNT->RETURN
							temp_res:=-count_ro(count_pq(eta[i],temp2[1],temp2[2],v1,v2,u1));
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
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
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
							return temp_res;
						else
							#COUNT->RETURN
							temp_res:=count_ro(count_pq(eta[i],temp2[2],temp2[1],v1,v2,u1));
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
							return temp_res;
						fi;										
					fi;
				
				elif temp=[v2] then
					
					if debug > 1 then
						Print("  ->intersection - v2\n");
					fi;

					if deg_f[v2]<deg_res[v2] then
						temp2:=IntersectionSet(Set(Flat(link(eta[i],[v2]))),U([eta[i+1],eta[i+2]]));
						if simp_ori(eta[i+1],temp_ori,[temp2[1],v2,temp2[2]])=1 then
							#COUNT->RETURN
							temp_res:=count_ro(count_pq(eta[i],temp2[2],temp2[1],u1,j,v2));
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
							return temp_res;
						else
							#COUNT->RETURN
							temp_res:=count_ro(count_pq(eta[i],temp2[1],temp2[2],u1,j,v2));
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
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
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
							return temp_res;
						else
							#COUNT->RETURN
							temp_res:=-count_ro(count_pq(eta[i],temp2[2],temp2[1],u1,j,v2));
							if debug > 0 then
								Print("decomposition -> return ",temp_res,"\n");
							fi;
							return temp_res;
						fi;										
					fi;
 				
 				elif temp=Set([u1,v2]) then
 				
 					if debug > 1 then
 						Print("  ->intersection - [u1,v2]\n");
 					fi;
 					
 					if deg_f[u1]<deg_res[u1] then
 				        	tempq:=deg_f[u1]-3;
 				        	tempp:=deg_f[v2]-3;
 				        	
 					 	temp_res:=count_ro([0,tempq])-count_ro([0,tempp]);
 				        	if debug > 0 then
 				        		Print("decomposition -> return ",temp_res,"\n");
 				        	fi;
 				        	return temp_res;
 					else
 						tempq:=deg_f[u1]-4;
 				        	tempp:=deg_f[v2]-2;
 				        	
 				        	temp_res:=-count_ro([0,tempq])+count_ro([0,tempp]);
 				        	if debug > 0 then
 				        		Print("decomposition -> return ",temp_res,"\n");
 				        	fi;
 				        	return temp_res;
 					fi;

 				elif temp=Set([u1,v1]) then
 					
 					if debug > 1 then
 						Print("  ->intersection - [u1,v1]\n");
 					fi;
 					
 					if deg_f[u1]<deg_res[u1] then
 				        	tempq:=deg_f[v1]-3;
 				        	tempp:=deg_f[u1]-3;
 				        	
 				        	temp_res:=count_ro([0,tempq])-count_ro([0,tempp]);
 				        	if debug > 0 then
 				        		Print("decomposition -> return ",temp_res,"\n");
 				        	fi;	        	
 				        	return temp_res;
 					else
 						tempq:=deg_f[v1]-2;
 				        	tempp:=deg_f[u1]-4;
 				        	
 				        	temp_res:=-count_ro([0,tempq])+count_ro([0,tempp]);
				        	if debug > 0 then
				        		Print("decomposition -> return ",temp_res,"\n");
				        	fi;
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
						
						if debug > 1 then
							Print("b=3 -> deg 4-5 - k=",k,", j=",j,"\n");
						fi;
						
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
				 				
								
								temp_res:=temp_res+count_value_ghi([eta[i+1],eta[i+4]],Set([v1,k]),edge,ori_eta[i+1]);
								
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
 								
 								temp_res:=temp_res+count_value_ghi([eta[i],eta[i+3]],Set([u,w]),edge,ori_eta[i]);

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
								
								temp_res:=temp_res+count_value_ghi([eta[i+6],eta[i+9]],Set([w1,w2]),edge,ori_eta[i+6]);
								
								if debug > 0 then
									Print("decomposition -> return ",temp_res,"\n");
								fi;
								
								return temp_res;
							fi;
						od;
					fi;
				od;
			fi;
		od;
	fi;

	if (difficulty_eta[i] mod 6) = 4 then
		if difficulty_eta[i]=2*difficulty_tri(eta[i]) then
		
			deg_f:=degree(eta[i-1]);
			deg_res:=degree(eta[i]);
			deg_ff:=deg_res;
			deg_ress:=degree(eta[i+1]);
			
			for element in Combinations(U([eta[i-1],eta[i]]),2) do
				if element in eta[i] and not element in eta[i-1] then
					sigma1:=Set(element);
				fi;
			od;
				
			for element in Combinations(U([eta[i],eta[i+1]]),2) do
				if element in eta[i] and not element in eta[i+1] then
					sigma2:=Set(element);
				fi;
			od;
			
			if Length(IntersectionSet(U([eta[i-1],eta[i]]),U([eta[i],eta[i+1]])))>2 then
			
				temp:=U([eta[i-1],eta[i]]);
				UniteSet(temp,U([eta[i],eta[i+1]]));
			
				tempve:=ve_count(eta[i]);
			
				for w in [1..Length(deg_ff)] do
					if deg_ff[w]=5 and not w in temp then
					
					
						# orientation for good notations
						temp_ori:=ori_spread(eta[i],ori_eta[i]);
						
						if deg_f[sigma1[1]]=5 then
							u1:=sigma1[1];
							v1:=sigma1[2];
						else
							v1:=sigma2[1];
							u1:=sigma2[2];
						fi;
						
						if simp_ori(eta[i],temp_ori,[v1,u1,link(eta[i],sigma1)[1]])=1 then
							w1:=Set(Flat(link(eta[i],sigma1)))[1];
							w2:=Set(Flat(link(eta[i],sigma1)))[2];
						else
							w1:=Set(Flat(link(eta[i],sigma1)))[2];
							w2:=Set(Flat(link(eta[i],sigma1)))[1];
						fi;
						
						if simp_ori(eta[i],temp_ori,[v2,u2,link(eta[i],sigma2)[1]])=1 then
							w3:=Set(Flat(link(eta[i],sigma2)))[1];
							w4:=Set(Flat(link(eta[i],sigma2)))[2];
						else
							w3:=Set(Flat(link(eta[i],sigma2)))[2];
							w4:=Set(Flat(link(eta[i],sigma2)))[1];
						fi;
					
					
						temp2:=[];
						for vertex in Flat(link(eta[i],[w])) do
							for vertex2 in Flat(link(eta[i],[w])) do
								temp1:=Set([vertex,vertex2]);
								if not temp1 in tempve[2] and Length(temp2)<4 then
									AddSet(temp2, temp1);
								fi;
							od;
						od;
												
						for edge in temp2 do
							if not (Set(Flat(link(eta[i-1],edge))) = Set([w1,w2]) and Set(Flat(link(eta[i+1],edge))) = Set([w3,w4])) then
								temp1:=edge;
								break;
							fi;
						od;
						
						temp_res:=count_value_ghi([eta[i-1],eta[i]],sigma1,edge,ori_eta[i-1])+count_value_ghi([eta[i],eta[i+1]],sigma2,edge,ori_eta[i]);
					
						u3:=Difference(temp1,[w])[1];
						
						if simp_ori(eta[i],temp_ori,[w,u3,link(eta[i],temp1)[1]])=1 then
							v3:=Flat(link(eta[i],temp1))[1];
							v4:=Flat(link(eta[i],temp1))[2];
						else
							v3:=Flat(link(eta[i],temp1))[2];
							v4:=Flat(link(eta[i],temp1))[1];
						fi;
						
						RemoveSet(eta[i], Set([u1,v1,w1]));
						RemoveSet(eta[i], Set([u1,v1,w2]));
						RemoveSet(eta[i], Set([w,u3,v4]));
						RemoveSet(eta[i], Set([w,u3,v3]));
						
						AddSet(eta[i], Set([u1,w1,w2]));
						AddSet(eta[i], Set([u1,v1,w2]));
						AddSet(eta[i], Set([v3,w,v4]));
						AddSet(eta[i], Set([v3,u3,v4]));
						
						temp4:=ShallowCopy(eta[i]);
						
						RemoveSet(temp4, Set([v3,w,v4]));
						RemoveSet(temp4, Set([v3,u3,v4]));
						
						AddSet(temp4, Set([w,u3,v4]));
						AddSet(temp4, Set([w,u3,v3]));
						
						temp5:=ShallowCopy(temp4);
						
						RemoveSet(temp5, Set([w3,u2,v2]));
						RemoveSet(temp5, Set([w4,u2,v2]));
						
						AddSet(temp5, Set([w3,v2,w4]));
						AddSet(temp5, Set([w3,u2,w4]));
						
						#change eta
					
						InsertElement(eta, temp4, i+1);
						InsertElement(eta, temp5, i+2);					
						
						#orientation
					
						ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i]);
						InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
	 					InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
					 					 	
						#p,q,r

						# so, 2 cycles
						
						if debug > 1 then
							Print("b=4 -> 2 cycles \n");
						fi;
						
						if debug > 0 then
							Print("decomposition -> return ",temp_res,"\n");
						fi;
						
						return temp_res;
					
					fi;
				od;
				
			elif Length(IntersectionSet(U([eta[i-1],eta[i]]),U([eta[i],eta[i+1]])))=2 then

				temp:=IntersectionSet(U([eta[i-1],eta[i]]),U([eta[i],eta[i+1]]));
			
				if  deg_res[temp[1]]=5 and deg_res[temp[2]]=5 then
				
					#EXTRA CASE
					
					if sigma1[1] in temp then
						v1:=sigma1[1];
						u1:=sigma1[2];
					else
						v1:=sigma1[2];
						u1:=sigma1[1];
					fi;
					
					if sigma2[1] in temp then
						v2:=sigma2[1];
						u2:=sigma2[2];
					else
						v2:=sigma2[2];
						u2:=sigma2[1];
					fi;
					
					w1:=Difference(Set(Flat(link(eta[i],Set([u1,v1])))),[v2])[1];
					w2:=Difference(Set(Flat(link(eta[i],Set([u2,v2])))),[v1])[1];
					w3:=Difference(Set(Flat(link(eta[i],Set([u1,v2])))),[v1])[1];
					w4:=Difference(Set(Flat(link(eta[i],Set([u2,v1])))),[v2])[1];
					
					# p,q,r
					
					temp_res:=count_value_ghi([eta[i-1],eta[i]],Set([w1,v2]),Set([v1,w4]),ori_eta[i-1]) + count_value_ghi([eta[i],eta[i+1]],Set([u2,v2]),Set([v1,w4]),ori_eta[i]);
					
					##
					
					temp1:=StructuralCopy(eta[i-1]);
					
					RemoveSet(temp1,Set([v1,w1,w4]));
					RemoveSet(temp1,Set([v1,u2,w4]));
					AddSet(temp1,Set([v1,w1,u2]));
					AddSet(temp1,Set([u2,w1,w4]));
					
					temp2:=StructuralCopy(temp1);
					
					RemoveSet(temp2,Set([u1,w1,v2]));
					RemoveSet(temp2,Set([v1,v2,w1]));
					AddSet(temp2,Set([u1,v1,w1]));
					AddSet(temp2,Set([u1,v1,v2]));
					
					temp3:=StructuralCopy(temp2);
					
					RemoveSet(temp3,Set([u2,v1,v2]));
					RemoveSet(temp3,Set([u2,v2,w2]));
					AddSet(temp3,Set([v1,v2,w2]));
					AddSet(temp3,Set([v1,w2,u2]));
					
					# change eta
					
					eta[i]:=StructuralCopy(temp1);
					InsertElement(eta,temp2,i+1);
					InsertElement(eta,temp3,i+3);
					
					# orientation
					
					ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
					InsertElement(ori_eta,ori_check([eta[i],eta[i+1]],ori_eta[i]),i+1);
					InsertElement(ori_eta,ori_check([eta[i+1],eta[i+2]],ori_eta[i+1]),i+2);
					
					# p,q,r
					
					if debug > 1 then
						Print("b=4 -> extra case\n");
					fi;
					
					if debug > 0 then
						Print("decomposition -> return ",temp_res,"\n");
					fi;
					
					return temp_res;
				
				fi;
			
			else
			
				temp_res:=count_value_ghi([eta[i-1],eta[i]],sigma1,sigma2,ori_eta[i-1]);
				
				if deg_f[sigma1[1]]=5 then
					u1:=sigma1[1];
					v1:=sigma1[2];
				else
					v1:=sigma2[1];
					u1:=sigma2[2];
				fi;
				
				w1:=Set(Flat(link(eta[i],sigma1)))[1];
				w2:=Set(Flat(link(eta[i],sigma1)))[2];
				w3:=Set(Flat(link(eta[i],sigma2)))[1];
				w4:=Set(Flat(link(eta[i],sigma2)))[2];
				
				Remove(eta[i],Set([u1,v1,w1]));
				Remove(eta[i],Set([u1,v1,w2]));
				Remove(eta[i],Set([u2,v2,w3]));
				Remove(eta[i],Set([u2,v2,w4]));
				
				AddSet(eta[i],Set([u1,w1,w2]));
				AddSet(eta[i],Set([v1,w1,w2]));
				AddSet(eta[i],Set([u2,w3,w4]));
				AddSet(eta[i],Set([v2,w3,w4]));
				
				ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
				
				if debug > 1 then
					Print("b=4 -> 1 cycle \n");
				fi;
				
				if debug > 0 then
					Print("decomposition -> return ",temp_res,"\n");
				fi;
				return temp_res;
				
			fi;
		fi;		
	fi;

	if (difficulty_eta[i] mod 6) = 5 then
		deg_f:=degree(eta[i]);
		deg_res:=degree(eta[i+1]);
		
		if debug > 1 then
			Print("b=5\n");
		fi;
		
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
								if debug > 0 then
									Print("decomposition -> return ",0,"\n");
								fi;
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
									if debug > 0 then
										Print("decomposition -> return ",temp_res,"\n");
									fi;
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
									if debug > 0 then
										Print("decomposition -> return ",temp_res,"\n");
									fi;
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
									if debug > 0 then
										Print("decomposition -> return ",temp_res,"\n");
									fi;
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
									if debug > 0 then
										Print("decomposition -> return ",temp_res,"\n");
									fi;
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
									if debug > 0 then
										Print("decomposition -> return ",temp_res,"\n");
									fi;
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
									if debug > 0 then
										Print("decomposition -> return ",temp_res,"\n");
									fi;
									return temp_res;
								fi;
							elif temp=Set([v1,v]) then
								if deg_f[v]<deg_res[v] then
									temp_res:=count_ro([0,Length(link(eta[i],[v]))-3])-count_ro([0,Length(link(eta[i],[v1]))-3]);
									if debug > 0 then
										Print("decomposition -> return ",temp_res,"\n");
									fi;
									return temp_res;
								else
									temp_res:=-count_ro([0,Length(link(eta[i],[v]))-4])+count_ro([0,Length(link(eta[i],[v1]))-2]);
									if debug > 0 then
										Print("decomposition -> return ",temp_res,"\n");
									fi;
									return temp_res;
								fi;
							elif temp=Set([v,v2]) then
								if deg_f[v]<deg_res[v] then
									temp_res:=count_ro([0,Length(link(eta[i],[v2]))-3])-count_ro([0,Length(link(eta[i],[v]))-3]);
									if debug > 0 then
										Print("decomposition -> return ",temp_res,"\n");
									fi;
									return temp_res;
								else
									temp_res:=-count_ro([0,Length(link(eta[i],[v2]))-4])+count_ro([0,Length(link(eta[i],[v]))-2]);
									if debug > 0 then
										Print("decomposition -> return ",temp_res,"\n");
									fi;
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
			
			if debug > 1 then
				Print("b=6 - Intersection of U - ", temp3, "\n");
			fi;
								
			if temp3=[] then
				
				if debug > 0 then
					Print("decomposition -> return ",0,"\n");
				fi;
				
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
				
				if debug > 1 then
					Print("  ->intersection - 1 vertex - u=",u,"\n");
				fi;
				
				temp_res:=-count_ro(count_pq(eta[i],v2,v1,w2,w1,u));
			
				if debug > 0 then
					Print("decomposition -> return ",temp_res,"\n");
				fi;
				
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
						
				if debug > 1 then
					Print("  ->intersection - 2 vertices - u1=",u1,", u2=",u2,"\n");
				fi;
				
				
				temp_res:=-count_ro([0,Length(link(eta[i],[u1]))-2])+count_ro([0,Length(link(eta[i],[u2]))-2]);
				
				if debug > 0 then
					Print("decomposition -> return ",temp_res,"\n");
				fi;
				
				return temp_res;
				
			fi;
		fi;		
	fi;
od;

end;
