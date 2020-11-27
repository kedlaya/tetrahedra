/*
   This file generates maximal rational-angle line configurations. 
   To use, start Magma and type
       load "tetrahedra.m";
   to load all declarations, then 
       load "tetrahedra-compute.m";
   to perform the computations. (Execute time was about 14 hours on an Intel Xeon CPU E5-1620 v3 @ 3.50GHz.)
   
   Each "database" constructed below is a sequence whose n-th term database[n] contains S_n semidirect {+-1}^n orbit representatives for the subspaces corresponding to n-vector configurations.  They are separated according to the "priority" of the initial 4-vector configuration, as defined by inputSubspaceLists above; the advantage of this division is that in looping over possibilities for each other principal 4 x 4 minor, one does not need to consider possibilities of higher priority, so much time is saved. 

   totalDatabase is the union of all the results, excluding those configurations that are planar or that are planar except for one vector perpendicular to all others. 
   newDatabase is the same, except that n-vector configurations contained in n'-vector configurations for some n' > n are omitted.  In other words, newDatabase contains maximal n-vector configurations only. 
   DisplayDatabase(newDatabase) presents this data in a prettier form, as parametrized angle matrices.

   The "Profile" commands use the Magma profiler to see how much time is being used by the various subroutines, after a computation has been done. 
   
*/

ProfileReset(); 

time sporadicDatabase := DatabaseStartingWithGroup(1);
time Rubinstein0Database := DatabaseStartingWithGroup(2);
time HillDatabase := DatabaseStartingWithGroup(3);
time Rubinstein1Database := DatabaseStartingWithGroup(4);
time Rubinstein2Database := DatabaseStartingWithGroup(5);
time IdDatabase := DatabaseStartingWithGroup(6);

time totalDatabase := [ EliminateSubconjugates(EliminateDuplicates( sporadicDatabase[n] cat Rubinstein0Database[n] cat HillDatabase[n] cat Rubinstein1Database[n] cat Rubinstein2Database[n] cat IdDatabase[n])) : n in [1..maxsize]];
time newDatabase := MakeNew(totalDatabase);
time newSubspaces := &cat newDatabase;
time ReggeNew := NewListAfterRegge(totalDatabase);
time NiceReggeAngleMatrices := [ NiceReggeRepresentative(sub) : sub in ReggeNew ];

DisplayDatabase(newDatabase);

Print5AndUp(newDatabase);

Print4(NiceReggeAngleMatrices);

ProfilePrintByTotalTime(ProfileGraph());

