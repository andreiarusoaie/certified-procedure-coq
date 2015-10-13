
Formal proof of soundness in Coq of the ''prove'' procedure

Coq version: 8.4pl5

Folder content:
   - Makefile
   - README.txt
   - Coq files:
         * ml.v : Matching Logic axioms
	 * util.v : generic paths
	 * rl.v : Reachability Logic definitions
	 * derivatives.v : Derivatives definitions
	 * sound.v : the main Coq file; it contains the main lemmas and the theorem


Build:
   :-$ make

Clean:
   :-$ make clean
