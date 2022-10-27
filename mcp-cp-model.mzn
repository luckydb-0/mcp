include "circuit.mzn";
include "alldifferent.mzn";

% The number of couriers
int: couriers;

    % The number of Nodes, Node 0 corresponds to the depot
int: items;
int: n_points = items + 1; % Note: the error may be due to not giving the correct size to the decision variable array
int: start_point = items + 1;
    % Vehicle capacity
array[1..couriers] of int: load_size;
    % Decision variables, is arc ij part of a route?
array[1..couriers, 1..n_points, 1..n_points] of var 0..1: routes;
    % For commodity flow (?)
  array[1..couriers, 1..n_points] of var int: uu;

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
array[1..n_points, 1..n_points] of var int: dist = array2d(1..n_points, 1..n_points, [if i == j then 0 else manhattan(point_x[i], point_y[i], point_x[j],   point_y[j]) endif | i, j in 1..n_points]);

% Used distance matrix
array[NODES, NODES] of var int: distance = array2d(NODES,NODES,[           
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
array[NODES] of var int: load; % load when arriving at node n in NODES


% +++++++++++++++++++++++++++ CONSTRAINTS +++++++++++++++++++++++++++++++++
% Initialization
constraint forall(i in START)(
    predecessor[i] in END
);

constraint forall(i in END)(
    successor[i] in START
);

% Difference
constraint alldifferent(successor);
constraint alldifferent(predecessor);

% Coherence
constraint forall(i in 1..items union START)( % Could also be on whole NODES but it's redundant I think
    successor[predecessor[i]] = i
);

constraint forall(i in 1..items union END)( % Specular to above
    predecessor[successor[i]] = i
);

% constraint circuit(predecessor);
% constraint circuit(successor);

% Path
constraint forall(i in NODES)(
    vehicle[i] = vehicle[predecessor[i]]
);

constraint redundant_constraint(
    forall(i in NODES)(
        vehicle[i] = vehicle[successor[i]]
    )
);

% Load
% For simplicity it is represented as if the courier picks up the item when passing by the node
% Initial load is always 0 
constraint forall(i in START)(
    load[i] = 0
);

% Problematic constraint:
% the load at each node is the one of the current node plus the previous visited
constraint forall(i in 1..items union END)(
    load[i] = Size[i] + load[predecessor[i]]
);

constraint forall(i in END)(
    load[i] <= load_size[vehicle[i]]
);

% Cost function
var int: objective = sum(i in 1..items union END)(distance[predecessor[i], i]);

% Search
solve :: seq_search(
    [
      int_search(predecessor, first_fail, indomain_split, complete),
%       int_search(load, dom_w_deg, indomain_min, complete),
      int_search(load, first_fail, indomain_min, complete),
      int_search(vehicle, first_fail, indomain_split, complete),
    ]
) minimize objective;

% Output
output [
    "distance = ", show(distance), "\n",
    "predecessor = ", show(predecessor), "\n",
    "successor = ", show(successor), "\n",
    "objective = ", show(objective),"\n",
    "vehicle = ", show(vehicle),"\n",
    "load = ", show(load),"\n",
];

