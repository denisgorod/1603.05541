##########################################################################################################
####            This program computes the first Pontryagin class of a simplicial complex.             ####
####		To be run for the case of M^8_{15}, the triangulation of the quaternionic	      ####
####		projective plane, it needs the file Pontryagin-M_8^15.testobject.		      ####
####		To be run in the general case it needs a modified version of the program	      ####
####		BISTELLAR by Frank H. Lutz, TU Berlin, Germany. 				      ####
####												      ####
####		For any questions, remarks or suggestions contact the author at			      ####
####		denis.gorod@mi.ras.ru								      ####
##########################################################################################################

### Global variables ###

Pdim:=0;
Pfaces:=[];
Pori:=[];
P:=[];
Pt:=0;
PSC:=[];

Lk:=[];
link_ori:=[];

eta:=[];
cycle_eta:=[];
ori_eta:=[];

vertices:=[];
bisfaces:=[];
faces:=[];
sgn_eta:=[];


temp:=[];
cycle_ori_eta:=[];
count:=0;
invest:=[];

## Just variables ##

simplex:=[];

### Variables for different options

object:=1;	## 0 for user object from "Pontryagin.testobject", requires BISTELLAR (a bit modified to have all the necessary output, contact the author for the modified version).
		## 1 for M_8^15 - using the file "Pontryagin-M_8^15.testobject", 
		### BISTELLAR is not directly required, the input file already contains all BISTELLAR output

debug:=0;

### Log and input ###

# Input in format "Pfacets:= ... ;;"

log_Pfile:=String("Pontryagin.log");
if object = 0 then
	Pfile:=String("Pontryagin.testobject");
elif object = 1 then
	Pfile:=String("Pontryagin-M_8_15.testobject");
fi;

# Don't input to "BISTELLAR.testobject"

### Global functions ###

# Gamma2.g

### Begin the cycle ### Main body ###

Read(Pfile);
Read("Decomposition.g");
LoadPackage("simpcomp");

## Profile ##

#ProfileGlobalFunctions(true);
#ProfileOperationsAndMethods(true);
#ProfileFunctions(decomposition,count_pq,ori_check,ori_spread,difficulty_bis);

##

LogTo("Pontryagin.log");
Pfaces := faces_count(Pfacets);;
Pdim := Length(Pfacets[1]);;
Pori := ori_spread(Pfacets, [1,1]);;


for simplex in Pfaces[Pdim - 4] do

	if object = 0 then
	
		PrintTo("BISTELLAR.testobject","facets:=");
		AppendTo("BISTELLAR.testobject",link(Pfacets, simplex));
		AppendTo("BISTELLAR.testobject",";;");
	
		Read("BISTELLAR.g");
	
	elif object = 1 then
		
		bisfaces:=bisfaces_M_8_15[Position(Pfaces[Pdim-4],simplex)];
	
	fi;
		
	# Make a chain from output of BISTELLAR
	
	Lk:=link(Pfacets, simplex);

	link_ori:=ori_spread(Lk,[1,induce_ori_on_link(Pfacets, simplex, Pori)]);
	vertices:=Set(Flat(bisfaces));

	count:=count+1;
	invest:=[];
	Pt:=0;

	for vertex in vertices do
	
		Print("vertex changed - ",vertex,"\n");

		eta:=[];
		ori_eta:=[];
		cycle_eta:=[];
		cycle_ori_eta:=[];
		
		for i in [1 .. Length(bisfaces)] do
		
			temp:=[];
			
			for face in bisfaces[i] do
				if Length(Difference(face, [vertex])) = 3 then
					AddSet(temp, Difference(face, [vertex]));
				fi;
			od;
			
			if Length(temp)>0 and (Length(eta)=0 or temp<>eta[Length(eta)]) then

				Add(eta, temp);

			fi;


		od;

		# Make the cycle

		temp:=ShallowCopy(link(Lk,[vertex]));
		
		while (temp<>0) do
			Add(cycle_eta, StructuralCopy(temp));
			temp:=cycle(temp);
		od;
		
		# Reversing + orientation
		
		ori_eta[1]:=[1,induce_ori_on_link(Lk, [vertex], link_ori)];
		
		for i in [2..Length(eta)] do
			ori_eta[i]:=ori_check([eta[i-1],eta[i]],ori_eta[i-1]);
		od;
		
		eta:=ReverseList(eta);
		ori_eta:=ReverseList(ori_eta);
		
		Remove(eta);
		Remove(ori_eta);
		
		cycle_ori_eta[1]:=[1,induce_ori_on_link(Lk, [vertex], link_ori)];
		
		for i in [2..Length(cycle_eta)] do
			cycle_ori_eta[i]:=ori_check([cycle_eta[i-1],cycle_eta[i]],cycle_ori_eta[i-1]);
		od;
		
		Append(eta,cycle_eta);
		Append(ori_eta,cycle_ori_eta);
		
		is_well_oriented(eta,ori_eta);
		
		# Decomposing for every vertex separately
		
		temp:=Pt;

		while max_vertex_eta(eta)>5 do
		
			Print("simplex #",count," - ",simplex,"\n");
			#Print("vertex - ",vertex,"\n");
			
			duplicate_free_eta(eta,ori_eta);
			
			if max_vertex_eta(eta)<=5 then
				break;
			fi;
			
			#is_well_oriented(eta,ori_eta);

			Pt:=Pt+decomposition(eta,ori_eta);
			
			#is_well_oriented(eta,ori_eta);

			#print_U_eta(eta);
			#Print("Maximal number of vertices - ", max_vertex_eta(eta),"\n");
			#Print("Length of ori_eta - ",Length(ori_eta),"\n");
			#Print("ori_eta - ",ori_eta,"\n");
			#Print("Length of eta - ",Length(eta),"\n");
			
		od;
		
		Print("Investment from vertex ",vertex," is ",Pt-temp,"\n");
		invest[vertex]:=Pt-temp;
		Print("invest=",invest,"\n");

	od;
	
	P[Position(Pfaces[Pdim-4],simplex)]:=[Pt,simplex];
	
	Print("eta computed\n");
	
od;
	
#	# Make the cycle with the recursion
#	
#	# Make from eta a cycle respecting vertex numeration
#	
#	# eta:=relabeling(eta); # relabeled
#	
#	# eta:=correction(eta); # now the first and last flips also have same vertex numerations
#	
#	# Decompose it, count the sum
	
#	for i in [1 .. Maximum(difficulty_eta)] do
#		
#		P:=P+decomposition(eta);
#		# break the cycle in case the difficulty (the number of flips in the cycle) drops too low
#	
#	od;
	
	# Do the trivial cases (base of decomposition)

	# 4 or 5 vertices

# Now make the chain representing the dual Pontryagin class
# No duality, just make the chain

PSC:=SC(Pfacets);

# The next is valid only for the case H^4 = Z. This part is easily rewritten in the general case.

PHomologyBasis:=SCHomologyBasisAsSimplices(PSC,Pdim-5)[1][2];

P5Boundaries:=[];

if Length(PHomologyBasis)=0 then 
	
	Print("No 4th cohomologies - p1=0\n");

elif Length(PHomologyBasis)=1 then 
	
	for simplex in Pfaces[Pdim-3] do
		Add(P5Boundaries, SCBoundarySimplex(simplex,true));
	od;

	PHBvector:=ListWithIdenticalEntries(Length(Pfaces[Pdim - 4]),0);;
	P5Bvector:=[];;
	Pvector:=ListWithIdenticalEntries(Length(Pfaces[Pdim - 4]),0);;

	for element in PHomologyBasis do
		PHBvector[Position(Pfaces[Pdim - 4],element[2])]:=element[1];
	od;

	for element in P do
		Pvector[Position(Pfaces[Pdim - 4],element[2])]:=element[1];
	od;

	for i in [1 .. Length(P5Boundaries)] do
		P5Bvector[i]:=ListWithIdenticalEntries(Length(Pfaces[Pdim - 4]),0);
		for element in P5Boundaries[i] do
			P5Bvector[i][Position(Pfaces[Pdim - 4],element[2])]:=element[1];
		od;
	od;

	Add(P5Bvector, PHBvector);;

	TransposedMat(P5Bvector);;

	Print(SolutionMat(P5Bvector, Pvector));  	#The last number in the received vector is the proportionality coefficient 
							#for the first Pontryagin class if the

fi;
# SCBoundarySimplex(simplex,orientation(+-,false))

#ProfileGlobalFunctions(false);
#ProfileOperationsAndMethods(false);
#UnprofileFunctions(decomposition,count_pq,ori_check,ori_spread,difficulty_bis);

