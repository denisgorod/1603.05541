# Audits every sub-case of the b = 4 branch of decomposition().
#
# The icosahedron has 12 vertices, all of degree 5, so difficulty_tri = 38.
# Flipping any edge drops two vertices to degree 4, giving the neighbour
# difficulty_tri = 37 and difficulty_bis = 2*38 = 76 = 4 mod 6.  Each of the 435
# edge pairs therefore yields a b = 4 configuration; padding the chain with a
# repeat on each side puts the peak at an interior position, as in a real eta.
#
# M^8_15 never reaches b = 4 (0 occurrences over all 3003 of its 4-simplices),
# so this is the only way to exercise that branch.
#
# For each sub-case the driver loop is run until the chain leaves b = 4, and the
# chain is audited after every step: every entry must still be a 2-sphere, every
# consecutive pair must still be one bistellar move apart, and the orientation
# must still spread consistently.  Returning a rational is not enough -- a
# sub-case that corrupts eta is reported as BROKEN CHAIN.
#
# Run from the repository root:
#   gap -q -b -A -c 'DECOMP:="Decomposition.g";;' tests/b4-cases.g


Read(DECOMP); Read("tests/b4-lib.g");

# Classify an edge pair into the b = 4 sub-case it drives.  This mirrors the
# dispatch in decomposition() exactly: v is the degree-5 end of each sigma and u
# the other end, the last case is v1 and v2 joined by an edge, and it splits on
# whether the edge u1u2 = {w1,u2} is already present.  (Naming v1/v2 by
# membership of U1 cap U2 instead -- the pre-rewrite convention -- puts the
# u1u2-present configurations in the wrong bucket.)
#
# Note that on these two spheres every configuration landing in the
# u1u2-PRESENT bucket has sigma1 and sigma2 sharing a vertex, so u1u2 lies in
# a triangle with sigma1, gamma(L,sigma1,u1u2) is undefined, and the branch
# correctly falls back to the generic auxiliary edge. The genuine case --
# sigma1 and sigma2 disjoint, u1u2 admissible -- is covered separately by
# tests/b4-case-p.g, which builds it rather than searching for it.
bucket := function(L, L1, L2, s1, s2)
    local E, deg, v1, u1, v2, u2, w1, w4;
    E := ve_count(L)[2]; deg := degree(L);
    if deg[s1[1]] = 5 then v1:=s1[1]; u1:=s1[2]; else v1:=s1[2]; u1:=s1[1]; fi;
    if deg[s2[1]] = 5 then v2:=s2[1]; u2:=s2[2]; else v2:=s2[2]; u2:=s2[1]; fi;
    if not Set([v1,v2]) in E then return "generic (v1v2 not an edge)"; fi;
    w1 := Difference(Set(Flat(link(L,s1))),[v2]);
    w4 := Difference(Set(Flat(link(L,Set([u2,v1])))),[v2]);
    if Length(w1) <> 1 or Length(w4) <> 1 then
        return "generic (w1 or w4 degenerate)";
    fi;
    if Set([w1[1],u2]) in E then return "last case, u1u2 PRESENT";
    else return "last case, u1u2 absent"; fi;
end;;

# Run the driver loop on one configuration, auditing the chain after every step.
drive := function(L, L1, L2)
    local e, o, k, steps, val, tot, st, d0, d;
    e := [StructuralCopy(L1),StructuralCopy(L1),StructuralCopy(L),
          StructuralCopy(L2),StructuralCopy(L2)];
    o := []; o[1] := [1,1];
    for k in [2..5] do
        o[k] := CALL_WITH_CATCH(ori_check,[[e[k-1],e[k]],o[k-1]]);
        if o[k][1] <> true or Length(o[k]) < 2 then return rec(verdict:="setup: ori_check failed"); fi;
        o[k] := o[k][2];
    od;
    st := CALL_WITH_CATCH(chain_ok,[e,o]);
    if st[1] <> true then return rec(verdict:="setup: audit errored"); fi;
    if st[2] <> "ok" then return rec(verdict:=Concatenation("setup: ",st[2])); fi;
    d0 := max_diff(e);
    tot := 0; steps := 0;
    while max_diff(e) mod 6 = 4 and max_vertex_eta(e) > 5 and steps < 25 do
        duplicate_free_eta(e,o);
        if max_vertex_eta(e) <= 5 then break; fi;
        val := CALL_WITH_CATCH(decomposition,[e,o]);
        steps := steps + 1;
        if val[1] <> true then
            return rec(verdict:="ERROR in decomposition", detail:=String(val[2]), steps:=steps);
        fi;
        if not IsRat(val[2]) then
            return rec(verdict:="non-rational return", detail:=String(val[2]), steps:=steps);
        fi;
        tot := tot + val[2];
        st := CALL_WITH_CATCH(chain_ok,[e,o]);
        if st[1] <> true then return rec(verdict:="audit itself errored", steps:=steps); fi;
        if st[2] <> "ok" then return rec(verdict:=Concatenation("BROKEN CHAIN: ",st[2]), steps:=steps); fi;
    od;
    if steps >= 25 then return rec(verdict:="b=4 did not clear in 25 steps", steps:=steps); fi;
    if max_diff(e) mod 6 = 4 and max_vertex_eta(e) > 5 then return rec(verdict:="still b=4 after loop"); fi;
    d := max_diff(e);
    return rec(verdict:="ok", steps:=steps, total:=tot, d_before:=d0, d_after:=d);
end;;

CAP := 6;;
res := rec();;

# Two test objects: the icosahedron (all degree 5, highly symmetric, produces
# the paper's last case) and one subdivision of it (42 vertices of degree 5 and
# 6, less symmetric, produces configurations the icosahedron cannot).  For the
# larger sphere only a slice of the first edge is swept, to keep the run short.

for OBJ in [ ["icosahedron", ICO, 30], ["subdivided icosahedron", ICO2, 12] ] do

  plan := rec();;
  edges := ve_count(OBJ[2])[2];;

  for s1 in edges{[1..Minimum(OBJ[3],Length(edges))]} do
   for s2 in edges do
    if s1 < s2 then
      L1 := flip(OBJ[2],s1); L2 := flip(OBJ[2],s2);
      if L1 <> fail and L2 <> fail then
        b := Concatenation(OBJ[1], ": ", bucket(OBJ[2],L1,L2,s1,s2));
        if not IsBound(plan.(b)) then plan.(b) := []; fi;
        Add(plan.(b), [s1,s2]);
      fi;
    fi;
   od;
  od;

  for b in RecNames(plan) do
    res.(b) := rec(total:=Length(plan.(b)), n:=0, ok:=0, bad:=[], steps:=[]);
    for p in plan.(b){[1..Minimum(CAP,Length(plan.(b)))]} do
      L1 := flip(OBJ[2],p[1]); L2 := flip(OBJ[2],p[2]);
      r := drive(OBJ[2],L1,L2);
      res.(b).n := res.(b).n + 1;
      if r.verdict = "ok" then
        res.(b).ok := res.(b).ok + 1; Add(res.(b).steps, r.steps);
      else AddSet(res.(b).bad, r.verdict); fi;
    od;
  od;

od;

for b in RecNames(res) do
    Print("#B ", b, "\n");
    Print("#B     in bucket      : ", res.(b).total, "   driven: ", res.(b).n, "\n");
    Print("#B     passed audit   : ", res.(b).ok, "\n");
    if Length(res.(b).steps) > 0 then Print("#B     steps to finish: ", res.(b).steps, "\n"); fi;
    if Length(res.(b).bad) > 0 then
        for m in res.(b).bad do Print("#B     FAILURE: ", m, "\n"); od;
    fi;
od;
QUIT_GAP(0);
