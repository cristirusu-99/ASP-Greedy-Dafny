// might help: <assert sol[0..k+1][..|sol[0..k+1]|-1] == sol[0..k]


datatype Activity = Pair(actStart: int, actEnd: int)

predicate sortedByActEndPair(a1: Activity, a2: Activity)
{
    a1.actEnd <= a2.actEnd
}

predicate sortedByActEnd(s: seq<Activity>)
    requires validActivitiesSeq(s)
{
    forall i, j :: 0 <= i < j < |s| ==> sortedByActEndPair(s[i], s[j])
}

predicate method canBeTaken(taken: seq<Activity>, act: Activity)
    requires validActivitiesSeq(taken)
    requires validActivity(act)
{
    forall act' :: act' in taken ==> !overlappingActivities(act, act')
}

predicate method differentActivities(a1: Activity, a2: Activity)
    requires validActivity(a1) && validActivity(a2)
{
    a1.actStart != a2.actStart || a1.actEnd != a2.actEnd
}

predicate distinctActivitiesSeq(s: seq<Activity>)
    requires validActivitiesSeq(s)
{
    forall i, j :: 0 <= i < j < |s| ==> differentActivities(s[i], s[j])
}

//TO DO validActivity: start < end -> precond la toate metodele ~ DONE
predicate validActivity(act: Activity)
{
    act.actStart < act.actEnd
}

predicate validActivitiesSeq(activities: seq<Activity>)
{
    forall act :: act in activities ==> validActivity(act)
}

//TO DO rethink ~ clarification?
predicate method overlappingActivities(a1: Activity, a2: Activity)
    requires validActivity(a1)
    requires validActivity(a2)
{
    a1.actEnd >= a2.actStart && a1.actStart <= a2.actEnd 
}

predicate disjointActivitiesSeq(activities: seq<Activity>)
    requires validActivitiesSeq(activities)
{
    distinctActivitiesSeq(activities) &&
    forall i1, i2 :: 0 <= i1 < i2 < |activities| ==> !overlappingActivities(activities[i1], activities[i2])
}

predicate isSolution(taken: seq<Activity>, activities: seq<Activity>)
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
    // INTREBARE: dat fiind ca taken e o secventa de activitati valide si respecta linia 76
    // nu ar trebui sa se valideze si un <ensures sortedByActEnd(taken)>?
{
    // Intrebare: fac verificarea pentru multime de elemente disticte aici sau in <disjointActivitiesSeq>
    // sa fie ordonate crescator strart2 > end1, start3>end2,...
    disjointActivitiesSeq(taken) &&
    (forall i1, i2 :: 0 <= i1 < i2 < |taken| ==> taken[i2].actStart > taken[i1].actEnd) &&
    forall act :: act in taken ==> act in activities
}

function castig(solution: seq<Activity>): int
    requires validActivitiesSeq(solution)
{
    |solution|
}

predicate optimalSolution(taken: seq<Activity>, activities: seq<Activity>)
    requires |activities| >= 0
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
{
    isSolution(taken, activities) &&
    forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities) ==> castig(taken) >= castig(sol) 
}

predicate isAfter(sol1:seq<Activity>, sol2:seq<Activity>)
    requires validActivitiesSeq(sol1)
    requires validActivitiesSeq(sol2)
{
    forall act1, act2 :: act1 in sol1 && act2 in sol2 ==> act1.actStart > act2.actEnd
}

predicate isOptimalAfter(sol:seq<Activity>, activities:seq<Activity>, taken:seq<Activity>)
    requires validActivitiesSeq(sol)
    requires validActivitiesSeq(activities)
    requires validActivitiesSeq(taken)
{
    isSolution(sol, activities) && isAfter(sol, taken) &&
    forall solp :: validActivitiesSeq(solp) && isSolution(solp, activities) && isAfter(solp, taken)
        ==> castig(sol) >= castig(solp)
}

lemma emptySolutionForEmptyEntry(taken: seq<Activity>, activities: seq<Activity>)
    requires taken == []
    requires activities == []
    ensures optimalSolution(taken, activities)
{
    assert isSolution(taken, activities);
    // !!! pentru a 
    forall sol:seq<Activity> | validActivitiesSeq(sol) && isSolution(sol, activities)
    ensures sol == []
    {
        if (sol != [])
        {
            var x := sol[0];
            assert x in activities;
            assert false;
        }
    }
}

lemma solWithoutIndexIsSol(taken: seq<Activity>, activities: seq<Activity>, index: int)
    requires |activities| > 0
    requires 0 <= index < |taken|
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
    requires sortedByActEnd(activities)
    requires isSolution(taken, activities)
    ensures isSolution(taken[..index]+taken[index+1..], activities)
{// trivial
}

lemma equalWinForOptimalSolution(optSol1: seq<Activity>, optSol2: seq<Activity>, activities: seq<Activity>)
    requires |activities| > 0
    requires validActivitiesSeq(optSol1)
    requires validActivitiesSeq(optSol2)
    requires validActivitiesSeq(activities)
    requires sortedByActEnd(activities)
    requires optimalSolution(optSol1, activities)
    requires optimalSolution(optSol2, activities)
    ensures castig(optSol1) == castig(optSol2)
{
    forall sol: seq<Activity> | validActivitiesSeq(sol) && isSolution(sol, activities)
    ensures castig(optSol1) >= castig(sol) && castig(optSol2) >= castig(sol)
    {
        if (optimalSolution(sol, activities))
        {
            assert castig(optSol1) == castig(sol) && castig(optSol2) == castig(sol);
        }
    }
}

lemma partOptimalPlusOptimalAfterMakesGlobalOptimal(taken: seq<Activity>, optAfter: seq<Activity>, activities: seq<Activity>, index: int)
    requires 0 <= index <|activities|
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(optAfter)
    requires validActivitiesSeq(activities)
    requires sortedByActEnd(activities)
    requires optimalSolution(taken, activities[..index])
    requires isOptimalAfter(optAfter, activities, taken)
    ensures optimalSolution(taken + optAfter, activities)
{
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index]) ==> castig(taken) >= castig(sol);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[index..]) && isAfter(sol, taken)
        ==> castig(optAfter) >= castig(sol);
    forall sol: seq<Activity> | validActivitiesSeq(sol) && isSolution(sol, activities[index..]) && disjointActivitiesSeq(sol + taken)
    ensures isAfter(sol, taken)
    {
        assert forall act :: act in activities[..index] ==> act.actEnd <= activities[index].actEnd;
        assert forall act :: act in taken ==> act in activities[..index];
        assert forall act :: act in taken ==> act.actEnd <= activities[index].actEnd;
        assume false;
    }
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[index..]) && disjointActivitiesSeq(sol + taken)
        ==> isAfter(sol, taken);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[index..]) && disjointActivitiesSeq(sol + taken)
        ==> castig(optAfter) >= castig(sol);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities) ==> castig(taken + optAfter) >= castig(sol);
}

    // Problema: momentan functioneaza, dar e posibil sa apara probleme dupa adaugarea conditiilor pentru multimi de
// elemente distincte pe <taken> si <activities>
lemma leadsToOptimalWithTaking(taken: seq<Activity>, activities: seq<Activity>, index: int)
    requires |activities| > 0
    requires 0 <= index < |activities|
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
    requires validActivity(activities[index])
    requires sortedByActEnd(activities)
    requires optimalSolution(taken, activities[..index])
    requires canBeTaken(taken, activities[index])
    requires forall i :: 0 <= i < |taken| ==> !overlappingActivities(taken[i], activities[index])
    ensures optimalSolution(taken+[activities[index]], activities[..index+1])
{
    // assert 
    assert canBeTaken(taken, activities[index]) ==> isAfter([activities[index]], taken);
    assert exists sol :: validActivitiesSeq(sol) && isOptimalAfter(sol, activities[..index+1], taken);
    // assert optimalSolution(taken, activities[..index]);
    // assert forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
    //     ==> optimalSolution(taken + optSol, activities);

    // assume isAfter([activities[index]], taken);
    // // var maybeSol := taken+[activities[index]];
    // // assert disjointActivitiesSeq(maybeSol);
    // // assert forall i1, i2 :: 0 <= i1 < i2 < |maybeSol| ==> maybeSol[i2].actStart > maybeSol[i1].actEnd;
    // // assert forall act :: act in maybeSol ==> act in activities[..index+1];
    // assert isSolution(taken+[activities[index]], activities[..index+1]);
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index]) ==> |taken| >= |sol|;
    // assert |taken + [activities[index]]| == |taken| + 1;
    // assert optimalSolution(taken, activities[..index]);
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index]) ==> |sol| <= |taken|;
    // // de ce nu merge daca nu repet assertul urmator de 2 ori?
    // forall sol:seq<Activity>, k:int | validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
    // ensures isSolution(sol[..k] + sol[k+1..], activities[..index]);
    // {
    //     solWithoutIndexIsSol(sol, activities[..index+1], index);
    // }
    // // assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
    // //         && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
    // //     ==> disjointActivitiesSeq(sol[..k] + sol[k+1..]);
    // // assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
    // //         && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
    // //     ==> disjointActivitiesSeq(sol[..k] + sol[k+1..]);
    // // //!!!v
    // // assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
    // //         && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
    // //     ==> forall act :: act in sol[..k] ==> act in activities[..index];
    // // //!!!v
    // // assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
    // //         && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
    // //     ==> forall act :: act in sol[k+1..] ==> act in activities[..index];
    // // assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
    // //         && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
    // //     ==> forall act :: act in sol[..k] + sol[k+1..] ==> act in activities[..index];
    // // assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
    // //         && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
    // //     ==> isSolution(sol[..k] + sol[k+1..], activities[..index]);
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
    //     ==> activities[index] in sol || activities[index] !in sol;
    // assert exists sol :: (validActivitiesSeq(sol) && isSolution(sol, activities[..index]) 
    //     ==> |sol| > |taken|);
    // assert exists sol :: (validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
    //     ==> |sol| >= |taken| + 1);
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
    //     ==> |sol| <= |taken| + 1;
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
    //     ==> |taken + [activities[index]]| >= |sol|;
}

lemma asdf(taken: seq<Activity>, activities: seq<Activity>, index: int)
    requires 0 <= index < |activities|
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
    requires validActivity(activities[index])
    requires sortedByActEnd(activities)
    requires forall sol :: validActivitiesSeq(sol) && optimalSolution(sol, activities[..index+1]) ==> castig(taken) >= castig(sol)
    ensures forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) ==> castig(taken) >= castig(sol)
{
    
}

lemma leadsToOptimalWithoutTaking(taken: seq<Activity>, activities: seq<Activity>, index: int)
    // requires |activities| > 0
    requires 0 <= index < |activities|
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
    requires validActivity(activities[index])
    requires sortedByActEnd(activities)
    requires optimalSolution(taken, activities[..index])
    requires !canBeTaken(taken, activities[index])
    ensures optimalSolution(taken, activities[..index+1])
{
    assert isSolution(taken, activities[..index+1]);
    forall sol: seq<Activity> | validActivitiesSeq(sol) && optimalSolution(sol, activities[..index+1])
    ensures castig(sol) <= castig(taken)
    {
        if activities[index] in sol
        {
        //     assert forall i1, i2 :: 0 <= i1 < i2 < |taken| ==> sol[i2].actStart > sol[i1].actEnd && validActivity(sol[i1]) && validActivity(sol[i2])
        //         ==> sortedByActEnd(sol);
        //     var k :| 0 <= k < |sol| && sol[k] == activities[index];
        //     var solWithoutK := sol[..k] + sol[k+1..];

        //     assert distinctActivitiesSeq(sol);
        //     solWithoutIndexIsSol(sol, activities[..index+1], k);
        //     assert isSolution(solWithoutK, activities[..index+1]);
        //     assert activities[index] !in  activities[..index];
        //     // Problema!!!
        //     //  - probabil am nevoie de o lema care sa spuna ca "fie oricare 2 sol, S1 si S2, optime pentru aceleasi date de intrare
        //     //      atunci castig(S1) == castig(S2)" - necesar
        //     // assert castig(sol)
        //     assert forall solp :: validActivitiesSeq(solp) && isSolution(solp, activities[..index]) ==> castig(taken) >= castig(solp);
        //     assert forall solp :: validActivitiesSeq(solp) && isSolution(solp, activities[..index]) ==> castig(solWithoutK) >= castig(solp);

        //     assert optimalSolution(solWithoutK, activities[..index]);
        //     assert false;
            assert optimalSolution(sol, activities[..index+1]);
        }
        else
        {
            assert isSolution(sol, activities[..index]);
        }
    }
    asdf(taken, activities, index);
    assert isSolution(taken, activities[..index+1]);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) ==> castig(taken) >= castig(sol);
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) && activities[index] in sol ==> castig(taken) >= castig(sol);
    // pentru orice sol optima S pana la index+1, vedem daca ultima activitate face sau nu parte
    // if ultima activitate face parte din sol opt S
    // then S-ultima act trebuie sa fie optima pentru activities[..index]
    // else isSolution(S, activities[..index]) && optimalSolution(S, activities[..index]) ==> |S| == |taken| ==> optimalSolution(taken, activities[..index+1])
}

//!!! de demonstrat !!!
lemma existsOptSolAfter(activities: seq<Activity>, taken: seq<Activity>)
    requires validActivitiesSeq(activities)
    requires validActivitiesSeq(taken)
    ensures exists optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
{
//     assert exists optSol :: validActivitiesSeq(optSol);

// //  fail!
//     assume exists optSol :: validActivitiesSeq(optSol) && disjointActivitiesSeq(optSol);
//     assume exists optSol:seq<Activity> :: forall i1, i2 :: 0 <= i1 < i2 < |optSol| ==> optSol[i2].actStart > optSol[i1].actEnd;
//     assume exists optSol:seq<Activity> :: forall act :: act in optSol ==> act in activities;

//     assert exists optSol :: validActivitiesSeq(optSol) && isSolution(optSol, activities);
// //  fail!
//     assert exists optSol :: isAfter(optSol, taken);
// //  fail!
//     assert exists optSol :: (forall solp :: validActivitiesSeq(solp) && isSolution(solp, activities) && isAfter(solp, taken)
//                                 ==> castig(optSol) >= castig(solp));

//     assert exists optSol :: isOptimalAfter(optSol, activities, taken);
    assume false;
}

lemma associativity(taken: seq<Activity>, act: Activity, optAfter: seq<Activity>)
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(optAfter)
    ensures (taken + [act]) + optAfter == taken + ([act] + optAfter)
{// trivial
} 

lemma subseqOfSolAfterIsSolAfterBase(activities: seq<Activity>, taken: seq<Activity>, solAfter: seq<Activity>)
    requires validActivitiesSeq(activities)
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(solAfter)
    requires isSolution(taken, activities)
    requires isSolution(solAfter, activities)
    requires isAfter(solAfter, taken)
    ensures forall i :: 0 <= i < |solAfter| ==> isSolution(solAfter[i..], activities) && isAfter(solAfter[i..], taken)
{// trivial
}


lemma ifSolIsAfterAddingSolsStaysDisjoint(activities: seq<Activity>, sol1: seq<Activity>, sol2: seq<Activity>)
    requires validActivitiesSeq(activities)
    requires validActivitiesSeq(sol1)
    requires validActivitiesSeq(sol2)
    requires disjointActivitiesSeq(sol1)
    requires disjointActivitiesSeq(sol2)
    requires isSolution(sol1, activities)
    requires isSolution(sol2, activities)
    requires isAfter(sol1, sol2)
    ensures disjointActivitiesSeq(sol2 + sol1)
{
    if sol1 == []
    {
        if sol2 == []
        {
            assert sol2 + sol1 == [];
            assert disjointActivitiesSeq([]);
            assert disjointActivitiesSeq(sol2 + sol1);
        }
        else
        {
            assert sol2 + sol1 == sol2;
            assert disjointActivitiesSeq(sol2);
            assert disjointActivitiesSeq(sol2 + sol1);
        }
    }
    else
    {
        
        if sol2 == []
        {
            assert sol2 + sol1 == sol1;
            assert disjointActivitiesSeq(sol1);
            assert disjointActivitiesSeq(sol2 + sol1);
        }
        else
        {
            assert forall act1, act2 :: act1 in sol1 && act2 in sol2 ==> act1.actStart > act2.actEnd;
            assert forall i1, i2 :: 0 <= i1 < i2 < |sol1| ==> sol1[i1].actEnd < sol1[i2].actStart;
            assert forall i1, i2 :: 0 <= i1 < i2 < |sol2| ==> sol2[i1].actEnd < sol2[i2].actStart;
            assert sol2[|sol2|-1].actEnd < sol1[0].actStart;
            assert forall i :: 0 <= i < |sol1| ==> sol2[|sol2|-1].actEnd < sol1[i].actStart;

            var maybeSol := sol2 + sol1;
            assert distinctActivitiesSeq(maybeSol);
            assert forall i1, i2 :: 0 <= i1 < i2 < |maybeSol| ==> maybeSol[i1].actEnd < maybeSol[i2].actStart;
            assert forall i1, i2 :: 0 <= i1 < i2 < |maybeSol| ==> !overlappingActivities(maybeSol[i1], maybeSol[i2]);

            assert disjointActivitiesSeq(sol2 + sol1);
        }
    }
}

lemma subseqOfSolAfterIsSolAfterExtended(activities: seq<Activity>, taken: seq<Activity>, solAfter: seq<Activity>)
    requires validActivitiesSeq(activities)
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(solAfter)
    requires isSolution(taken, activities)
    requires isSolution(solAfter, activities)
    requires isAfter(solAfter, taken)
    ensures forall i :: 0 <= i < |solAfter| ==> isSolution(solAfter[i..], activities) && isSolution(taken + solAfter[..i], activities)
        && isAfter(solAfter[i..], taken + solAfter[..i])
{
    assert forall i :: 0 <= i < |solAfter| ==> isSolution(solAfter[i..], activities);

    assert forall at, aa :: at in taken && aa in solAfter ==> aa.actStart > at.actEnd;
    assert forall i :: 0 <= i < |solAfter| ==> isAfter(solAfter[..i], taken);

    forall  i: int | 0 <= i < |solAfter|
    ensures isSolution(taken + solAfter[..i], activities)
    {
        var maybeSol := taken + solAfter[..i];
        assert isAfter(solAfter[..i], taken);
        assert disjointActivitiesSeq(solAfter[..i]);
        ifSolIsAfterAddingSolsStaysDisjoint(activities, solAfter[..i], taken);
        assert disjointActivitiesSeq(maybeSol);
        assert forall i1, i2 :: 0 <= i1 < i2 < |maybeSol| ==> maybeSol[i2].actStart > maybeSol[i1].actEnd;
        assert forall act :: act in maybeSol ==> act in activities;
    }

    assert forall i :: 0 <= i < |solAfter| ==> isSolution(taken + solAfter[..i], activities);
    assert forall i :: 0 <= i < |solAfter| ==> isAfter(solAfter[i..], taken + solAfter[..i]);
}

ghost method helperL1(optSolp: seq<Activity>, sol2p: seq<Activity>, sol2: seq<Activity>, activities: seq<Activity>, index: int, taken: seq<Activity>)
    requires 0 <= index < |activities|
    requires |sol2p| > 0
    requires |sol2| > 1
    requires validActivitiesSeq(optSolp)
    requires validActivitiesSeq(sol2p)
    requires validActivitiesSeq(sol2)
    requires validActivitiesSeq(activities)
    requires sortedByActEnd(activities)
    requires validActivitiesSeq(taken)
    requires canBeTaken(taken, activities[index])
    requires isOptimalAfter(optSolp, activities, taken + [activities[index]])
    requires isOptimalAfter(sol2, activities, taken)
    requires optimalSolution(taken, activities[..index])
    requires forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
        ==> optimalSolution(taken + optSol, activities)
    requires !isOptimalAfter([activities[index]] + optSolp, activities, taken)
    ensures false;
{
    assert sol2[0].actEnd < sol2[1].actStart;
    assert validActivity(sol2[1]);
    // assert sol2[1].actStart < sol2[1].actEnd;
    assert validActivity(sol2[0]);
    assert sol2[0].actEnd < sol2[1].actEnd;
    assert taken[|taken|-1].actEnd < sol2[0].actStart;
    assert sol2[0].actStart < sol2[0].actEnd;
    // sol2[i].start > taken[j].end, orice i, j
    assert forall i, j :: 0<=i<|sol2| && 0<=j<|taken| ==> sol2[i].actStart > taken[j].actEnd;
    // acts[index].start > taken[-1].end, deoarece canBeTaken
    assert forall act :: act in activities[..index] ==> act.actEnd <= activities[index].actEnd;
    assert forall i :: 0 <= i < |taken|-1 ==> taken[i].actEnd < taken[|taken|-1].actStart;
    assert validActivity(taken[|taken|-1]);
    // assert taken[|taken|-1].actStart < taken[|taken|-1].actEnd;
    assert forall i :: 0 <= i < |taken|-1 ==> taken[i].actEnd < taken[|taken|-1].actEnd;
    // because isSolution
    assert forall i, j :: 0 <= i < j < |taken| ==> taken[i].actEnd < taken[j].actStart;
    // because validActivitiesSeq
    assert forall i :: 0 <= i < |taken| ==> taken[i].actStart < taken[i].actEnd;

    assert forall act :: act in taken ==> act.actEnd < activities[index].actStart || act.actStart > activities[index].actEnd;
    assert forall i, j :: 0 <= i < j < |taken| ==> taken[i].actStart < taken[i].actEnd < taken[j].actStart < taken[j].actEnd;
    assume forall act :: act in taken ==> act.actEnd < activities[index].actEnd;
    // assert forall act :: act in taken ==>
    assert activities[index].actStart > taken[|taken|-1].actEnd;
    
    // acts[index].end <= sol2[0].end
    assert activities[index].actEnd <= sol2[0].actEnd;
    assert isAfter(sol2[1..], [activities[index]]);
    ifSolIsAfterAddingSolsStaysDisjoint(activities, sol2[1..], [activities[index]]);
    assert isOptimalAfter(sol2p, activities, taken);

    // !!! v
    assert activities[index] in sol2p && castig(sol2p) > 1 + castig(optSolp);

    assert castig(sol2p[1..]) > castig(optSolp);
}

lemma optimalSubstructure(sol: seq<Activity>, taken: seq<Activity>, activities: seq<Activity>)
    requires validActivitiesSeq(sol)
    requires validActivitiesSeq(taken)
    requires validActivitiesSeq(activities)
    requires isOptimalAfter(sol, activities, taken)
    requires isSolution(taken, activities)
    ensures forall i :: 0 <= i < |sol| ==> isOptimalAfter(sol[i..], activities, taken + sol[..i])
{
}

lemma helperL3a(optSolp: seq<Activity>, activities: seq<Activity>, index: int, taken: seq<Activity>)
    requires 0 <= index < |activities|
    requires validActivitiesSeq(optSolp)
    requires validActivitiesSeq(activities)
    requires sortedByActEnd(activities)
    requires validActivitiesSeq(taken)
    requires canBeTaken(taken, activities[index])
    requires optimalSolution(taken, activities[..index])
    requires forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
        ==> optimalSolution(taken + optSol, activities)
    requires isOptimalAfter(optSolp, activities, taken + [activities[index]])
    requires !isOptimalAfter([activities[index]] + optSolp, activities, taken)
    ensures false
{
    existsOptSolAfter(activities, taken);
    var sol2:seq<Activity> :| validActivitiesSeq(sol2) && isOptimalAfter(sol2, activities, taken);
    var sol2p:seq<Activity> := [activities[index]] + sol2[1..];

    assert disjointActivitiesSeq(sol2[1..]);
    // !!! v
    assert |sol2| > 1 ==> sol2[0].actEnd < sol2[1].actEnd;
    if |sol2| > 1
    {
        assert castig(sol2) == castig(sol2p);
        // assert isOptimalAfter(sol2p, activities, taken);
        // helperL1(optSolp, sol2p, sol2, activities, index, taken);

        assert sol2[0].actEnd < sol2[1].actStart;
        assert validActivity(sol2[1]);
        // // assert sol2[1].actStart < sol2[1].actEnd;
        assert validActivity(sol2[0]);
        assert sol2[0].actEnd < sol2[1].actEnd;
        assert forall i :: 0 <= i < |taken| ==> taken[i].actEnd < sol2[0].actStart;
        assert sol2[0].actStart < sol2[0].actEnd;
        // // sol2[i].start > taken[j].end, orice i, j
        assert forall i, j :: 0<=i<|sol2| && 0<=j<|taken| ==> sol2[i].actStart > taken[j].actEnd;
        // // acts[index].start > taken[-1].end, deoarece canBeTaken
        assert forall act :: act in activities[..index] ==> act.actEnd <= activities[index].actEnd;
        assert forall i :: 0 <= i < |taken|-1 ==> taken[i].actEnd < taken[|taken|-1].actStart;
        assert forall i :: 0 <= i < |taken| ==> validActivity(taken[i]);
        // // because isSolution
        assert forall i, j :: 0 <= i < j < |taken| ==> taken[i].actEnd < taken[j].actStart;
        // // because validActivitiesSeq
        assert forall i :: 0 <= i < |taken| ==> taken[i].actStart < taken[i].actEnd;
        assert forall i, j :: 0 <= i < j < |taken| ==> taken[i].actStart < taken[i].actEnd < taken[j].actStart < taken[j].actEnd;

        // assert forall a: Activity, b: Activity :: validActivity(a) && validActivity(b) && !overlappingActivities(a, b) ==> overlappingActivities(b, a);
        assert forall act :: act in taken ==> !overlappingActivities(activities[index], act);
        assert forall act :: act in taken ==> act.actEnd < activities[index].actEnd;
        // // assert forall act :: act in taken ==>
        assert forall i :: 0 <= i < |taken| ==> taken[i].actEnd < activities[index].actStart;

        assert forall i, j :: 0 <= i < |taken| && 0 <= j < |sol2| ==> taken[i].actEnd < sol2[j].actStart;

        assert isSolution(sol2, activities[index..]);
        
        // // acts[index].end <= sol2[0].end
        // assert activities[index].actEnd <= sol2[0].actEnd;
        // assume isAfter(sol2[1..], [activities[index]]);
        // ifSolIsAfterAddingSolsStaysDisjoint(activities, sol2[1..], [activities[index]]);
        // assert isOptimalAfter(sol2p, activities, taken);

        // // !!! v
        // assert activities[index] in sol2p && castig(sol2p) > 1 + castig(optSolp);

        // assert castig(sol2p[1..]) > castig(optSolp);

        assume false;
    }
    else
    {
        assume false;
    }
}

ghost method helperL4a(optSolp: seq<Activity>, activities: seq<Activity>, index: int, taken: seq<Activity>)
    requires 0 <= index < |activities|
    requires validActivitiesSeq(optSolp)
    requires validActivitiesSeq(activities)
    requires sortedByActEnd(activities)
    requires validActivitiesSeq(taken)
    requires sortedByActEnd(taken)
    requires canBeTaken(taken, activities[index])
    requires optimalSolution(taken, activities[..index])
    requires forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
        ==> optimalSolution(taken + optSol, activities)
    requires isOptimalAfter(optSolp, activities, taken + [activities[index]])
    requires !optimalSolution(taken + [activities[index]] + optSolp, activities)
    ensures false
{
    if !isOptimalAfter([activities[index]] + optSolp, activities, taken)
    {
        helperL3a(optSolp, activities, index, taken);
        assert false;
    }
    else
    {
        assert false;
    }
}

ghost method helperL5(optSolp: seq<Activity>, activities: seq<Activity>, index: int, taken: seq<Activity>)
    requires 0 <= index < |activities|
    requires validActivitiesSeq(optSolp)
    requires validActivitiesSeq(activities)
    requires sortedByActEnd(activities)
    requires validActivitiesSeq(taken)
    requires sortedByActEnd(taken)
    requires canBeTaken(taken, activities[index])
    requires forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
        ==> optimalSolution(taken + optSol, activities)
    requires isOptimalAfter(optSolp, activities, taken + [activities[index]])
    requires optimalSolution(taken, activities[..index])
    ensures optimalSolution(taken + [activities[index]] + optSolp, activities)
{
    if !optimalSolution(taken + [activities[index]] + optSolp, activities)
    {
        helperL4a(optSolp, activities, index, taken);
        assert false;
    }
}

lemma lema1(activities: seq<Activity>, taken: seq<Activity>, index: int)
    requires 0 <= index < |activities|
    requires validActivitiesSeq(activities)
    requires validActivitiesSeq(taken)
    requires sortedByActEnd(activities)
    requires sortedByActEnd(taken)
    requires optimalSolution(taken, activities[..index])
    requires forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
        ==> optimalSolution(taken + optSol, activities)
    requires canBeTaken(taken, activities[index])
    ensures forall optSolp :: validActivitiesSeq(optSolp) && isOptimalAfter(optSolp, activities, taken + [activities[index]])
                ==> optimalSolution(taken + [activities[index]] + optSolp, activities)
{
    forall optSolp: seq<Activity> | validActivitiesSeq(optSolp) && isOptimalAfter(optSolp, activities, taken + [activities[index]])
    ensures optimalSolution(taken + [activities[index]] + optSolp, activities);
    {
        helperL5(optSolp, activities, index, taken);
    }
}


method ASPGreedy(activities: seq<Activity>) returns (taken: seq<Activity>)
    requires |activities| > 0
    requires validActivitiesSeq(activities)
    requires distinctActivitiesSeq(activities)
    requires sortedByActEnd(activities)
    ensures validActivitiesSeq(taken)
    ensures disjointActivitiesSeq(taken)
    ensures optimalSolution(taken, activities)
{
    var seqLen := |activities|;
    taken := [];
    emptySolutionForEmptyEntry(taken, activities[..0]);
    var index := 0;
    assert forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
            ==> optimalSolution(taken + optSol, activities);
    while index < |activities|
        decreases seqLen - index
        invariant seqLen == |activities|
        invariant 0 <= index <= |activities|
        invariant validActivitiesSeq(taken)
        invariant disjointActivitiesSeq(taken)
        invariant isSolution(taken, activities[..index])
        invariant optimalSolution(taken, activities[..index])
        invariant forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
            ==> optimalSolution(taken + optSol, activities)
    {
        if canBeTaken(taken, activities[index])
        {
            assert forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
                ==> optimalSolution(taken + optSol, activities);

            leadsToOptimalWithTaking(taken, activities, index);
            lema1(activities, taken, index);
            
            taken := taken + [activities[index]];
            index := index + 1;
            assert optimalSolution(taken, activities[..index]);

            assert forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
                ==> optimalSolution(taken + optSol, activities);
        }
        else
        {
            assert 0 <= index;
            assert index < |activities|;
            leadsToOptimalWithoutTaking(taken, activities, index);
            assert forall optSol :: validActivitiesSeq(optSol) && isOptimalAfter(optSol, activities, taken)
                ==> optimalSolution(taken + optSol, activities);
            index := index + 1;
            assert optimalSolution(taken, activities[..index]);
        }
    }
}