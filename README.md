# TTP-2
This code solves the traveling tournament problem with maximum tour length two (TTP-2).

① Our source code is written by c/c++. When the number of teams satisfies n>=8, it can genetate a good schedule for TTP-2.

② There are 62 benckmark instances on the website https://mat.gsia.cmu.edu/TOURN/. Our experiment contains 33 instances of them. 

③ There are two .cpp files, where the ttp algorithms are the same but the heuristc methods are different: 
   the first applies the first swapping rule and the second swapping rule once, respectively; 
   the second alternatively applies the first swapping rule and the second swapping rule until it hits a total running time 60 seconds 
     (note that we shall restart the algorithm if both the swapping rules fail to improve the solution and the running time is still less than 60 seconds).

④ If you want to run an instance, say "Galaxy10", you need to set "n=10", read the distance matrix "Galaxy10.txt", 
   and then run the function "get_schedule(int target, pair<int, int> *u, vector<vector<int> > &D, int n, int FFF, int &min, vector<vector<int> > &day, int f_check, int opt_flag)":
       "int target": it may be used to find a shcule with a result of target (usually we set target=0, since we want to find the smallest possible result);
       "pair<int, int> *u": the minimum weight matching;
       "vector<vector<int> > &D": the distance matrix;
       "int n": the number of teams;
       "int FFF": usually set FFF=1 (if set FFF=-1, the edges between super-teams will be reversed, and it also can generate a schedule of TTP-2; in the second set, if we restart the algorithm, we may set FFF=-FFF)
       "int &min": the current obtained best result (initally set min=INT_MAX)
       "vector<vector<int> > &day": it may be used to return a schedule (we usually only cares the result of it and do not show the schedule)
       "int f_check": usually set f_check=0 (our algorithm always can generate feasible solutions, so it is needless to check the correctness)
       "int opt_flag": usually set opt_flag=1 (the flag of the heuristic)

⑤ Our code mainly consists of three main parts: the well-known minimum weight perfect matching algorithm, the schedule algorithms, and the swapping heuristics.

⑥ You can run .cpp directly, the input has already been given, and it will show you the 33 results generated by our algorithm with the running time:
   the first .cpp will show the 33 tested results in the first set (the running time is within 4 seconds); 
   the second .cpp will show the 33 tested results in the second set (the running time is about 33 miniutes, 1 miniute each instance).

⑦ The random seed is set as: srand(0). (If the seed changes, the results may be better/worse). Note that different environments may generate (slightly) different results in the second set (even using srand(0)).
