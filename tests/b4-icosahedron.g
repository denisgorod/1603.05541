# Exercises the b = 4 branch of decomposition() (difficulty = 4 mod 6).
#
# The icosahedron has 12 vertices, all of degree 5, so difficulty_tri = 3*12+2
# = 38.  Flipping any edge drops two vertices to degree 4, giving the neighbour
# difficulty_tri = 37, so difficulty_bis = 2*38 = 76 and 76 mod 6 = 4.  Padding
# the chain with a repeat on each side puts the peak at an interior position,
# as it is in a real eta, and leaves the flanking pairs at difficulty 75.
#
# M^8_15 never reaches b = 4 (0 occurrences over the first 120 of its 3003
# 4-simplices), so this is the only way to run that branch at all.
#
# Run with:  gap -q -b -A -c 'DECOMP:="Decomposition.g";;' tests/b4-icosahedron.g

# degree 5) and reports which of its two sub-branches each configuration takes.
Read(DECOMP);
ICO := Set(List([[1,2,3],[1,3,4],[1,4,5],[1,5,6],[1,2,6],
        [2,3,8],[3,4,9],[4,5,10],[5,6,11],[2,6,7],
        [2,7,8],[3,8,9],[4,9,10],[5,10,11],[6,7,11],
        [7,8,12],[8,9,12],[9,10,12],[10,11,12],[7,11,12]], Set));;
flip := function(L, e)
    local lk, M;
    lk := Set(Flat(link(L,e)));
    if Length(lk) <> 2 or lk in ve_count(L)[2] then return fail; fi;
    M := StructuralCopy(L);
    RemoveSet(M,Set([e[1],e[2],lk[1]])); RemoveSet(M,Set([e[1],e[2],lk[2]]));
    AddSet(M,Set([lk[1],lk[2],e[1]]));   AddSet(M,Set([lk[1],lk[2],e[2]]));
    return M; end;;
edges := ve_count(ICO)[2];; dist := [];; hits := [];;
for s1 in edges do for s2 in edges do if s1 < s2 then
  L1 := flip(ICO,s1); L2 := flip(ICO,s2);
  if L1 <> fail and L2 <> fail then
    n := Length(IntersectionSet(U([L1,ICO]),U([ICO,L2])));
    if not IsBound(dist[n+1]) then dist[n+1] := 0; fi;
    dist[n+1] := dist[n+1] + 1;
    if n = 2 then Add(hits,[s1,s2]); fi;
  fi;
fi; od; od;
Print("#T |U1 cap U2| distribution (index = size+1): ", dist, "\n");
Print("#T configurations with |U1 cap U2| = 2 : ", Length(hits), "\n");

ok:=0;; err:=0;; msgs:=[];;
for h in hits do
  L1 := flip(ICO,h[1]); L2 := flip(ICO,h[2]);
  e := [StructuralCopy(L1),StructuralCopy(L1),StructuralCopy(ICO),
        StructuralCopy(L2),StructuralCopy(L2)];
  o := []; o[1] := [1,1];
  for k in [2..5] do o[k] := ori_check([e[k-1],e[k]],o[k-1]); od;
  r := CALL_WITH_CATCH(decomposition,[e,o]);
  if r[1] then ok:=ok+1; else err:=err+1; AddSet(msgs,String(r[2])); fi;
od;
Print("#T last-case runs OK  : ", ok, "\n");
Print("#T last-case errored  : ", err, "\n");
for m in msgs do Print("#T   error: ", m, "\n"); od;
QUIT_GAP(0);
