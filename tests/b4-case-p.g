# Checks the one b = 4 sub-case that no naturally occurring test object reaches:
# the paper's last case with the edge u1u2 already present in L.
#
# Neither the icosahedron nor its subdivision contains that configuration, and a
# 1500-step walk over minimum-degree-5 spheres did not reach one either, so the
# patch from the figure on p. 368 is built directly instead. Because it is built
# rather than found, its minimum degree is 3 and decomposition() would dispatch
# it to b = 6; the branch's decision path is therefore replayed here against the
# real helpers (flip_defined, flip_edge, count_with_intersection, ori_check) and
# the resulting chain is put through the same audit as tests/b4-cases.g.
#
# Run from the repository root:
#   gap -q -b -A -c 'DECOMP:="Decomposition.g";;' tests/b4-case-p.g

Read(DECOMP); Read("tests/b4-lib.g");

# star(v1) = 3-2-5-6-4 and star(v2) = 3-1-5-7-8, so v1 = 1 and v2 = 2 both have
# degree 5 and are adjacent; the hexagon 5-6-4-3-8-7 left over is filled so that
# the chord {4,5} -- the figure's u1u2 -- is present.
#
#   figure  sigma1  sigma2  v1  v2  u1  u2  w   u1u2
#   here    {1,3}   {2,5}    1   2   4   5   6   {4,5}
#   code    sigma1  sigma2  v1  v2  w1  u2  w4  [w1,u2]

CASE_P_L := Set(List(
    [[1,2,3],[1,2,5],[1,5,6],[1,4,6],[1,3,4],[2,5,7],
     [2,7,8],[2,3,8],[4,5,6],[3,4,5],[3,5,8],[5,7,8]], Set));;

ok := 0;; fail_ := 0;;
check := function(name, cond)
    if cond then ok := ok + 1; Print("#P pass  ", name, "\n");
    else fail_ := fail_ + 1; Print("#P FAIL  ", name, "\n"); fi;
end;;

check("L is a 2-sphere", is_sphere(CASE_P_L));

L    := CASE_P_L;;
edgs := ve_count(L)[2];;
deg  := degree(L);;
s1   := Set([1,3]);;      # sigma1
s2   := Set([2,5]);;      # sigma2

check("sigma1 and sigma2 are disjoint", Length(IntersectionSet(s1,s2)) = 0);
check("flip of sigma1 is defined",      flip_defined(L,s1));
check("flip of sigma2 is defined",      flip_defined(L,s2));

# Naming, exactly as the branch does it: v is the degree-5 end of each sigma.
if deg[s1[1]] = 5 then v1:=s1[1]; u1:=s1[2]; else v1:=s1[2]; u1:=s1[1]; fi;;
if deg[s2[1]] = 5 then v2:=s2[1]; u2:=s2[2]; else v2:=s2[2]; u2:=s2[1]; fi;;

check("v1 has degree 5", deg[v1] = 5);
check("v2 has degree 5", deg[v2] = 5);
check("v1v2 is an edge, so the last case applies", Set([v1,v2]) in edgs);

w1 := Difference(Set(Flat(link(L,s1))),[v2]);;
w4 := Difference(Set(Flat(link(L,Set([u2,v1])))),[v2]);;
check("w1 is well defined", Length(w1) = 1);
check("w4 is well defined", Length(w4) = 1);

e := Set([w1[1],u2]);;
check("u1u2 = [w1,u2] is already an edge of L, so this is the PRESENT half",
      e in edgs);

L1 := flip_edge(L,s1);;
L2 := flip_edge(L,s2);;

check("L1 is a 2-sphere", is_sphere(L1));
check("L2 is a 2-sphere", is_sphere(L2));

# Admissibility of e, the test the branch applies to its candidates.
check("flip of e defined in L1", flip_defined(L1,e));
check("flip of e defined in L",  flip_defined(L,e));
check("flip of e defined in L2", flip_defined(L2,e));
check("no simplex of L holds both e and sigma1",
      not ForAny(L, t -> IsSubsetSet(t,e) and IsSubsetSet(t,s1)));
check("no simplex of L holds both e and sigma2",
      not ForAny(L, t -> IsSubsetSet(t,e) and IsSubsetSet(t,s2)));

# The construction: eta[i-1] <- eta[i] -> eta[i+1] becomes
# eta[i-1] -> flip_e(eta[i-1]) -> flip_e(eta[i]) -> flip_e(eta[i+1]) -> eta[i+1].
eta := [ StructuralCopy(L1), StructuralCopy(L1), StructuralCopy(L),
         StructuralCopy(L2), StructuralCopy(L2) ];;
ori := [];; ori[1] := [1,1];;
for k in [2..5] do ori[k] := ori_check([eta[k-1],eta[k]], ori[k-1]); od;;
check("setup chain is valid", chain_ok(eta,ori) = "ok");

i := 3;;
val := count_with_intersection([eta[i-1],eta[i]],Set(Flat(link(eta[i],s1))),e,ori[i-1])
     + count_with_intersection([eta[i],eta[i+1]],s2,e,ori[i]);;
val := -val;;                      # the PRESENT half carries the opposite sign
check("value is rational", IsRat(val));
Print("#P   value = ", val, "\n");

# All three flipped spheres are computed before eta is touched, as the branch
# does -- taking them lazily after the first assignment reads shifted indices.
t3 := flip_edge(eta[i-1],e);;
t4 := flip_edge(eta[i],  e);;
t5 := flip_edge(eta[i+1],e);;
eta[i] := t3;;
InsertElement(eta, t4, i+1);;
InsertElement(eta, t5, i+2);;
ori[i] := ori_check([eta[i-1],eta[i]],ori[i-1]);;
InsertElement(ori, ori_check([eta[i],eta[i+1]],ori[i]), i+1);;
InsertElement(ori, ori_check([eta[i+1],eta[i+2]],ori[i+1]), i+2);;

Print("#P   chain after: ", chain_ok(eta,ori), "\n");
check("chain is still valid after the construction", chain_ok(eta,ori) = "ok");
check("L no longer appears in the chain", not L in eta);

Print("#P ", ok, " passed, ", fail_, " failed\n");
QUIT_GAP(0);
