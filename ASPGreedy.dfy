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
    forall i1, i2 :: 0 <= i1 < i2 < |activities| ==> !overlappingActivities(activities[i1], activities[i2])
}

predicate isSolution(takenActivities: seq<Activity>, activities: seq<Activity>)
    requires validActivitiesSeq(takenActivities)
    requires validActivitiesSeq(activities)
{
    // Intrebare: fac verificarea pentru multime de elemente disticte aici sau in <disjointActivitiesSeq>
    disjointActivitiesSeq(takenActivities) && //|takenActivities| <= |activities| &&
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
    assert !exists sol :: sol != [] && validActivitiesSeq(sol) && isSolution(sol, activities);
    assert exists sol :: validActivitiesSeq(sol) && isSolution(sol, []) && castig(takenActivities) <= castig(sol);
    assert exists sol :: sol == [] && isSolution(sol, []);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities) ==> castig(takenActivities) >= castig(sol);
}

// Problema: momentan functioneaza, dar e posibil sa apara probleme dupa adaugarea conditiilor pentru multimi de elemente distincte pe <takenActivities> si <activities>
lemma leadsToOptimal(takenActivities: seq<Activity>, activities: seq<Activity>, index: int)
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
    //TO DO revazut predicate si modificat ~ DONE
    // assert validActivitiesSeq(takenActivities+[activities[index]]);
    // assert validActivitiesSeq(activities[..index]);
    // assert disjointActivitiesSeq(takenActivities+[activities[index]]);
    assert isSolution(takenActivities+[activities[index]], activities[..index+1]);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index]) ==> |takenActivities| >= |sol|;
    assert |takenActivities + [activities[index]]| == |takenActivities| + 1;
    assert optimalSolution(takenActivities, activities[..index]);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index]) ==> |sol| <= |takenActivities|;
    assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
            ==> disjointActivitiesSeq(sol[..k] + sol[k+1..]);
    assert forall sol, k :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) && activities[index] in sol && 0 <= k < |sol| && sol[k] == activities[index]
            ==> isSolution(sol[..k] + sol[k+1..], activities[..index]);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
            ==> activities[index] in sol || activities[index] !in sol;
    // assert |takenActivities| <= |activities[..index]|;
    // assert |takenActivities + [activities[index]]| <= |activities[..index+1]|;
    // assert |takenActivities| + 1 <= |activities[..index+1]|;
    // assert forall sol :: validActivitiesSeq(sol) && disjointActivitiesSeq(sol) && |sol| <= |activities[..index+1]| && forall act :: act in sol ==> act in activities[..index+1] 
    //         ==> |sol| <= |activities[..index+1]|;
    // assert forall sol :: validActivitiesSeq(sol) && disjointActivitiesSeq(sol) && |sol| <= |activities[..index+1]| && forall act :: act in sol ==> act in activities[..index+1] 
    //         ==> |sol| <= |takenActivities| + 1;
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
    //         ==> |sol| <= |activities[..index+1]|;
    assert exists sol :: (validActivitiesSeq(sol) && isSolution(sol, activities[..index]) 
            ==> |sol| > |takenActivities|);
    assert exists sol :: (validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
            ==> |sol| >= |takenActivities| + 1);
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
            ==> |sol| <= |takenActivities| + 1;
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index+1]) 
            ==> |takenActivities + [activities[index]]| >= |sol|;
}

// de redenumit: "leadsToOptimalWithoutTaking" ~ DONE
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
    assert validActivitiesSeq([]);
    assert disjointActivitiesSeq([]);
    assert forall act :: act in takenActivities ==> act in [];
    assert exists sol :: (validActivitiesSeq(sol) && isSolution(sol, []) ==> sol == []);
    assert exists sol :: (validActivitiesSeq(sol) && isSolution(sol, []) ==> sol != []);
    // de extras intr-o lema
    assume forall sol :: validActivitiesSeq(sol) && isSolution(sol, []) ==> sol == [];
    assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, []) ==> castig([]) >= castig(sol);
    assert optimalSolution([], []);
    assert validActivitiesSeq(takenActivities);
    leadsToOptimal(takenActivities, activities, 0);
    takenActivities := [activities[0]];
    var lastTaken := activities[0];
    var index := 1;
    // assert forall sol :: validActivitiesSeq(sol) && disjointActivitiesSeq(sol) && 
    //                         (forall i :: 0 <= i < |sol| ==> sol[i] in activities[..1])  
    //         ==> sol == [activities[0]] || sol == [];
    // assert forall sol :: validActivitiesSeq(sol) && isSolution(sol, activities[..index]) ==> sol == [activities[0]] || sol == [];
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
            leadsToOptimal(takenActivities, activities, index);
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