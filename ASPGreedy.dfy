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

predicate method canBeTaken(takenActivities: seq<Activity>, act: Activity)
    requires validActivitiesSeq(takenActivities)
    requires validActivity(act)
{
    forall act' :: act' in takenActivities ==> !overlappingActivities(act, act')
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

// predicate validActivitiesSet(activities: set<Activity>)
// {
//     forall act :: act in activities ==> validActivity(act)
// }

//TO DO rethink ~ clarification?
predicate method overlappingActivities(a1: Activity, a2: Activity)
    requires validActivity(a1)
    requires validActivity(a2)
{
    a1.actStart < a2.actEnd || a2.actStart < a1.actEnd
}

//TO DO modificat sa verifice pe indici ~ DONE
predicate disjointActivitiesSeq(activities: seq<Activity>)
    requires validActivitiesSeq(activities)
{
    distinctActivitiesSeq(activities) &&
    forall i1, i2 :: 0 <= i1 < i2 < |activities| ==> !overlappingActivities(activities[i1], activities[i2])
}

predicate isSolution(takenActivities: seq<Activity>, activities: seq<Activity>)
    requires validActivitiesSeq(takenActivities)
    requires validActivitiesSeq(activities)
{
    // Intrebare: fac verificarea pentru multime de elemente disticte aici sau in <disjointActivitiesSeq>
    disjointActivitiesSeq(takenActivities) &&
    forall act :: act in takenActivities ==> act in activities
}

function castig(solution: seq<Activity>): int
    requires validActivitiesSeq(solution)
{
    |solution|
}

predicate optimalSolution(takenActivities: seq<Activity>, activities: seq<Activity>)
    requires |activities| >= 0
    requires validActivitiesSeq(takenActivities)
    requires validActivitiesSeq(activities)
{
    isSolution(takenActivities, activities) &&
    forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities) ==> castig(takenActivities) >= castig(sol) 
}

lemma emptySolutionForEmptyEntry(takenActivities: seq<Activity>, activities: seq<Activity>)
    requires takenActivities == []
    requires activities == []
    ensures optimalSolution(takenActivities, activities)
{
    assert isSolution(takenActivities, activities);
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

    // Problema: momentan functioneaza, dar e posibil sa apara probleme dupa adaugarea conditiilor pentru multimi de
// elemente distincte pe <takenActivities> si <activities>
lemma leadsToOptimalWithTaking(takenActivities: seq<Activity>, activities: seq<Activity>, index: int)
    requires |activities| > 0
    requires 0 <= index < |activities|
    requires validActivitiesSeq(takenActivities)
    requires validActivitiesSeq(activities)
    requires validActivity(activities[index])
    requires sortedByActEnd(activities)
    requires optimalSolution(takenActivities, activities[..index])
    requires canBeTaken(takenActivities, activities[index])
    requires forall i :: 0 <= i < |takenActivities| ==> !overlappingActivities(takenActivities[i], activities[index])
    ensures optimalSolution(takenActivities+[activities[index]], activities[..index+1])
{
    assert isSolution(takenActivities+[activities[index]], activities[..index+1]);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index]) ==> |takenActivities| >= |sol|;
    assert |takenActivities + [activities[index]]| == |takenActivities| + 1;
    assert optimalSolution(takenActivities, activities[..index]);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index]) ==> |sol| <= |takenActivities|;
    // de ce nu merge daca nu repet assertul urmator de 2 ori?
    assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
            && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
        ==> disjointActivitiesSeq(sol[..k] + sol[k+1..]);
    assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
            && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
        ==> disjointActivitiesSeq(sol[..k] + sol[k+1..]);
    assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
            && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
        ==> forall act :: act in sol[..k] + sol[k+1..] ==> act in activities[..index];
    assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1])
            && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
        ==> isSolution(sol[..k] + sol[k+1..], activities[..index]);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
        ==> activities[index] in sol || activities[index] !in sol;
    assert exists sol :: (validActivitiesSeq(sol) && isSolution(sol, activities[..index]) 
        ==> |sol| > |takenActivities|);
    assert exists sol :: (validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
        ==> |sol| >= |takenActivities| + 1);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
        ==> |sol| <= |takenActivities| + 1;
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
        ==> |takenActivities + [activities[index]]| >= |sol|;
}

lemma leadsToOptimalWithoutTaking(takenActivities: seq<Activity>, activities: seq<Activity>, index: int)
    requires |activities| > 0
    requires 0 <= index < |activities|
    requires validActivitiesSeq(takenActivities)
    requires validActivitiesSeq(activities)
    requires validActivity(activities[index])
    requires sortedByActEnd(activities)
    requires optimalSolution(takenActivities, activities[..index])
    requires !canBeTaken(takenActivities, activities[index])
    ensures optimalSolution(takenActivities, activities[..index+1])
{
    assert isSolution(takenActivities, activities[..index+1]);
    forall sol: seq<Activity> | validActivitiesSeq(sol) && optimalSolution(sol, activities[..index+1])
    ensures castig(sol) <= castig(takenActivities)
    {
        if activities[index] in sol
        {
            var k :| 0 <= k < |sol| && sol[k] == activities[index];
            var solWithoutK := []; // sol - ultima activitate
            assert distinctActivitiesSeq(sol);
            assume forall i :: 0 <= i < |sol| ==> sol[i] in activities;
            if k == 0
            {
                assert [sol[k]] + sol[k+1..] == sol;
                solWithoutK := sol[k+1..];
            }
            else
            {
                assert |sol[..k]| == k;
                assert forall i :: 0 <= i < k ==> sol[i] in sol;
                assert sol[k] in sol;
                assert |sol[k+1..]| == |sol| - (k + 1);
                if k == |sol|-1
                {
                    assert sol[..k] + [sol[k]] == sol;
                    var solWithoutK := sol[..k];
                }
                else
                {
                    assert forall i :: k+1 <= i < |sol| ==> sol[i] in sol;
                    assert sol[..k] + [sol[k]] + sol[k+1..] == sol;
                    var solWithoutK := sol[..k] + sol[k+1..];
                }
            }
            assert isSolution(solWithoutK, activities[..index]);
            // Problema!!!
            assert forall solp :: validActivitiesSeq(solp) && isSolution(solp, activities[..index]) ==> castig(solWithoutK) >= castig(solp);

            assume optimalSolution(solWithoutK, activities[..index]);
            assume false;
        }
        else
        {
            assert isSolution(sol, activities[..index]) && optimalSolution(sol, activities[..index])
                ==> |sol| == |takenActivities|;
            assert true;
        }
    }
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) && activities[index] in sol ==> castig(takenActivities) >= castig(sol);
    // pentru orice sol optima S pana la index+1, vedem daca ultima activitate face sau nu parte
    // if ultima activitate face parte din sol opt S
    // then S-ultima act trebuie sa fie optima pentru activities[..index]
    // else isSolution(S, activities[..index]) && optimalSolution(S, activities[..index]) ==> |S| == |takenActivities| ==> optimalSolution(takenActivities, activities[..index+1])
}

method ASPGreedy(activities: seq<Activity>) returns (takenActivities: seq<Activity>)
    requires |activities| > 0
    requires validActivitiesSeq(activities)
    requires distinctActivitiesSeq(activities)
    requires sortedByActEnd(activities)
    ensures validActivitiesSeq(takenActivities)
    ensures disjointActivitiesSeq(takenActivities)
    ensures isSolution(takenActivities, activities)
{
    var seqLen := |activities|;
    takenActivities := [];
    // Problema: expresiile de forma <forall act :: act in takenAct ==> act in activities> nu garanteaza si ca |takenAct| <= |activities|
    // Cauza posibila: by-default <seq> permite duplicate si am modificat acum cateva saptamani <takenActivities> sa fie <seq>, pentru ca am nevoie de o verificare pe indecsi
    emptySolutionForEmptyEntry(takenActivities, activities[..0]);
    leadsToOptimalWithTaking(takenActivities, activities, 0);
    takenActivities := [activities[0]];
    var lastTaken := activities[0];
    var index := 1;
    assert optimalSolution(takenActivities, activities[..index]);
    while index < seqLen
        decreases seqLen - index
        invariant 0 < index <= seqLen
        invariant validActivitiesSeq(takenActivities)
        invariant disjointActivitiesSeq(takenActivities)
        invariant isSolution(takenActivities, activities[..index])
        invariant optimalSolution(takenActivities, activities[..index])
    {
        if canBeTaken(takenActivities, activities[index])
        {
            leadsToOptimalWithTaking(takenActivities, activities, index);
            takenActivities := takenActivities + [activities[index]];
            lastTaken := activities[index];
            index := index + 1;
            assert optimalSolution(takenActivities, activities[..index]);
        }
        else
        {
            leadsToOptimalWithoutTaking(takenActivities, activities, index);
            index := index + 1;
            assert optimalSolution(takenActivities, activities[..index]);
        }
    }
}