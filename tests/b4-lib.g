############################################################################
##  Validators shared by the b = 4 tests.
############################################################################

# A closed oriented 2-manifold of Euler characteristic 2, i.e. a 2-sphere:
# every edge in exactly two triangles, every vertex link a single cycle,
# connected, V - E + F = 2.
is_sphere := function(L)
    local vs, es, e, cnt, f, v, lk, seen, stack, x, y, nb;
    if Length(L) = 0 then return false; fi;
    if ForAny(L, f -> Length(f) <> 3) then return false; fi;
    vs := Set(Flat(L));
    es := ve_count(L)[2];
    for e in es do
        cnt := Number(L, f -> IsSubsetSet(f, e));
        if cnt <> 2 then return false; fi;
    od;
    if Length(vs) - Length(es) + Length(L) <> 2 then return false; fi;
    for v in vs do
        lk := link(L, [v]);                       # list of edges, as 2-sets
        if Length(lk) < 3 then return false; fi;
        if Length(Set(Flat(lk))) <> Length(lk) then return false; fi;   # #verts = #edges
        # link must be ONE cycle, not several
        nb := Set(Flat(lk));
        seen := [nb[1]]; stack := [nb[1]];
        while Length(stack) > 0 do
            x := Remove(stack);
            for e in lk do
                if x in e then
                    y := Difference(e, [x])[1];
                    if not y in seen then Add(seen, y); Add(stack, y); fi;
                fi;
            od;
        od;
        if Length(seen) <> Length(nb) then return false; fi;
    od;
    return true;
end;;

# One bistellar move apart (or identical).
is_move := function(L1, L2)
    local d1, d2, vs;
    if L1 = L2 then return true; fi;
    d1 := Difference(L1, L2); d2 := Difference(L2, L1);
    vs := Set(Concatenation(Flat(d1), Flat(d2)));
    if Length(vs) <> 4 then return false; fi;
    if Length(d1) = 2 and Length(d2) = 2 then return true; fi;   # edge flip
    if Length(d1) = 1 and Length(d2) = 3 then return true; fi;   # 0-move
    if Length(d1) = 3 and Length(d2) = 1 then return true; fi;   # 2-move
    return false;
end;;

# is_well_oriented, but returning a verdict instead of printing.
oriented_ok := function(eta, ori_eta)
    local i, o, sp;
    for i in [2..Length(eta)] do
        o := CALL_WITH_CATCH(ori_check, [[eta[i-1],eta[i]], ori_eta[i-1]]);
        if o[1] <> true or Length(o) < 2 then return false; fi;   # ori_check fell off
        o := o[2];
        if o = fail or o = [] then return false; fi;
        sp := CALL_WITH_CATCH(ori_spread, [eta[i], o]);
        if sp[1] <> true then return false; fi;
        sp := sp[2];
        if not IsBound(ori_eta[i]) or not IsBound(sp[ori_eta[i][1]]) then return false; fi;
        if sp[ori_eta[i][1]] <> ori_eta[i][2] then return false; fi;
    od;
    return true;
end;;

# Full structural audit of a chain.
chain_ok := function(eta, ori_eta)
    local i;
    if Length(eta) <> Length(ori_eta) then return "length(eta) <> length(ori_eta)"; fi;
    for i in [1..Length(eta)] do
        if not IsBound(eta[i]) then return Concatenation("eta[",String(i),"] unbound"); fi;
        if not is_sphere(eta[i]) then return Concatenation("eta[",String(i),"] not a 2-sphere"); fi;
        if not IsBound(ori_eta[i]) then return Concatenation("ori_eta[",String(i),"] unbound"); fi;
    od;
    for i in [1..Length(eta)-1] do
        if not is_move(eta[i], eta[i+1]) then
            return Concatenation("eta[",String(i),"]->eta[",String(i+1),"] is not a bistellar move");
        fi;
    od;
    if not oriented_ok(eta, ori_eta) then return "orientation inconsistent"; fi;
    return "ok";
end;;

max_diff := function(eta)
    return Maximum(List([1..Length(eta)-1], k -> difficulty_bis([eta[k],eta[k+1]])));
end;;

flip := function(L, e)
    local lk, M;
    lk := Set(Flat(link(L,e)));
    if Length(lk) <> 2 or lk in ve_count(L)[2] then return fail; fi;
    M := StructuralCopy(L);
    RemoveSet(M,Set([e[1],e[2],lk[1]])); RemoveSet(M,Set([e[1],e[2],lk[2]]));
    AddSet(M,Set([lk[1],lk[2],e[1]]));   AddSet(M,Set([lk[1],lk[2],e[2]]));
    return M;
end;;

ICO := Set(List([[1,2,3],[1,3,4],[1,4,5],[1,5,6],[1,2,6],
      [2,3,8],[3,4,9],[4,5,10],[5,6,11],[2,6,7],
      [2,7,8],[3,8,9],[4,9,10],[5,10,11],[6,7,11],
      [7,8,12],[8,9,12],[9,10,12],[10,11,12],[7,11,12]], Set));;
