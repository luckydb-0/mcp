include "circuit.mzn";
include "alldifferent.mzn";
include "bin_packing.mzn";

% The number of couriers
int: couriers;

    % The number of Nodes, Node 0 corresponds to the depot
int: items;
int: n_points = items + 1; % Note: the error may be due to not giving the correct size to the decision variable array
int: start_point = items + 1;
    % Vehicle capacity
array[1..couriers] of int: load_size;
    % Points coordinates
array[1..n_points] of int: point_x;
array[1..n_points] of int: point_y;
  % Each item size
array[1..items] of int: size;

set of int: NODES = 1..items+2*couriers; 
set of int: DEPOT_NODES = items+1..items+2*couriers;
set of int: START = items+1..items+couriers;
set of int: END = items+couriers+1..items+2*couriers;

%--------------------------------------------------------------------------

% Euclidean distance
function var float: euclidean(var int: x1, var int: y1, var int: x2, var int: y2) = sqrt((x1-x2)^2+(y1-y2)^2);

% Manhattan distance
function var int: manhattan(var int: x1, var int: y1, var int: x2, var int: y2) = abs(x1 - x2) + abs(y1 - y2);

% Initial distance matrix
array[1..n_points, 1..n_points] of var float: dist = array2d(1..n_points, 1..n_points, [if i == j then 0 else euclidean(point_x[i], point_y[i], point_x[j],   point_y[j]) endif | i, j in 1..n_points]);

% Used distance matrix
array[NODES, NODES] of var float: distance = array2d(NODES,NODES,[           
  if i<=items /\ j <= items then 
    dist[i,j]
  elseif i<=items /\ j>items then % customer-depot
    dist[i, start_point]
  elseif j<=items /\ i>items then % depot-customer
    dist[start_point, j]
  else 
    0 % depot-depot
  endif
   | i,j in NODES ]);  
   
% size array adapted for the solution with 0 value on ndoes representing the depot 
array[NODES] of int: Size = array1d(NODES, [if i <= items then size[i] else 0 endif | i in NODES]);

% Variables
array[NODES] of var NODES: successor; 
array[NODES] of var NODES: predecessor; % redundant predecessor variables
array[NODES] of var 1..couriers: vehicle; % which vehicle visits which customer?
int: load_limit = max(load_size);
array[NODES] of var 0..load_limit: load; % load when arriving at node n in NODES


var float: objective;

% ------ initialization constraints ---- %
% 1
constraint redundant_constraint(
   forall(n in (items+2..items+couriers)) (
     predecessor[n] = n + couriers-1
   )
);

% 2
constraint redundant_constraint(
   predecessor[items+1] = items+2*couriers
);

% successors of end nodes are start nodes
% 3
constraint 
   forall(n in (items+couriers+1..items+2*couriers-1)) (
     successor[n] = n-couriers+1 
   );
% 4
constraint
   successor[items+2*couriers] = items+1;

% associate each start/end nodes with a vehicle
% 5
constraint 
   forall(n in START) (
     vehicle[n] = n-items
   );
% 6
constraint 
   forall(n in END) (
     vehicle[n] = n-items-couriers
   );


% 8
% vehicle load when starting at the depot
constraint 
   forall(n in START) (
     load[n] = 0 % demand[n]
   );
   
% ------- predecessor/successor constraints --- %
% 9
constraint redundant_constraint(
   forall(n in NODES) (
      successor[predecessor[n]] = n
   )
);

% 10
constraint redundant_constraint(
   forall(n in NODES) (
      predecessor[successor[n]] = n
   )
);

 
% alldiff + subtour elimination constraints
% 11
constraint 
   circuit(successor);
% 12
constraint redundant_constraint(
   circuit(predecessor)
);

 
  % ---- vehicle constraints ------------- %

% vehicle of node i is the same as the vehicle for the predecessor
% 13
constraint redundant_constraint(
   forall(n in 1..items) (
      vehicle[predecessor[n]] = vehicle[n]
   )
);
% 14
constraint 
   forall(n in 1..items) (
      vehicle[successor[n]] = vehicle[n]
   );

 % ----- load constraints ------------ %

constraint 
   forall(n in 1..items) (
      load[n] + size[n] = load[successor[n]]
   );
constraint
   forall(n in START) (
      load[n] = load[successor[n]] 
   );

constraint
    forall(n in END)(
        load[n] <= load_size[vehicle[n]]
    );

% Bin packing constraints
% Note: try with whole vehicle and Size arrays
constraint bin_packing_capa(load_size, [vehicle[i] | i in 1..items ], [Size[i] | i in 1..items ]);


% Symmetry breaking
constraint
    lex_lesseq(predecessor, [ predecessor[i] | i in NODES ])
 /\ lex_lesseq(predecessor, [ predecessor[i] | i in reverse(NODES) ]);

% % /\  lex_lesseq(array1d(predecessor), [ predecessor[i,j] | i in reverse(1..NODES), j in 1..NODES ])
% % /\  lex_lesseq(array1d(predecessor), [ predecessor[j,i] | i in 1..NODES, j in reverse(1..NODES) ])
% % /\  lex_lesseq(array1d(predecessor), [ predecessor[i,j] | i in 1..NODES, j in reverse(1..NODES) ])
% % /\  lex_lesseq(array1d(predecessor), [ predecessor[j,i] | i in reverse(1..NODES), j in 1..NODES ])
% % /\  lex_lesseq(array1d(predecessor), [ predecessor[i,j] | i,j in reverse(1..NODES) ])
% % /\  lex_lesseq(array1d(predecessor), [ predecessor[j,i] | i,j in reverse(1..NODES) ])

constraint
    lex_lesseq(successor, [ successor[i] | i in NODES ])
 /\ lex_lesseq(successor, [ successor[i] | i in reverse(NODES) ]);

constraint
    lex_lesseq(vehicle, [ vehicle[i] | i in START ])
 /\ lex_lesseq(vehicle, [ vehicle[i] | i in reverse(START) ]);

constraint
    lex_lesseq(vehicle, [ vehicle[i] | i in END])
 /\ lex_lesseq(vehicle, [ vehicle[i] | i in reverse(END) ]);

% =====================================
% Objective
% =====================================

constraint objective = sum (n in 1..items union END) (distance[predecessor[n], n]);

solve :: seq_search([int_search([predecessor[j] | j in 1..items], dom_w_deg, indomain_split, complete),
               int_search([successor[j] | j in 1..items], dom_w_deg, indomain_random, complete),
               int_search([vehicle[j] | j in START], first_fail, indomain_split, complete),
               int_search([load[j] | j in END], first_fail, indomain_min, complete)
              ]) :: restart_luby(250) :: relax_and_reconstruct(predecessor, 80)
minimize objective; % distance
