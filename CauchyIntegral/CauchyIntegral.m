(* Mathematica package *)
(*
Copyright (c) 2012,Georg Wechslberger
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
Neither the name of the Technial University of Munich nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)
(* Error Messages *)
iterateUntilConvergence::maxIter="Maximum number of iterations (`1`) reached, estimated current precision is `2` "
iterateUntilConvergence::belowGoal="Could not reach PrecisionGoal (`1`) estimated Precision of result `2` "
contourCauchyIntegral::maxIter="Maximum number of iterations (`1`) reached. Consider increasing MaxIterations for a more accurate result."

(* public function *)
CauchyIntegralSEW::usage="CauchyIntegralSEW[f,n,z] calculates a contour for the Cauchy integral given by f,n and z, which optimizes its condition number."
CauchyIntegral::usage="CauchyIntegral[g,sew,f,n,z] evaluates the cauchy integral given by f,n and z along the path sew in the graph g."
CauchyIntegralD::usage="CauchyIntegralD[f,n,z] calcualtes the n-th derivative of f at z using Cauchy's integral formula."
SEWContourPlot::usage="SEWContourPlot[g,sew] creates a contour plot of the vertex weight of all vertices in g and plots the sew on top of it."

Begin["`Private`"]

(* some utility functions *)
Second = #[[2]]&;

relErr[x_,y_] = ( Norm[x-y]/Norm[y] ) //Log10;
relErr[x_,x_] := -Precision[x];

selectPosition[l_List,f_] := Pick[l//Length//Range,f/@l];

findShortestCircle[gin_,p_,opts:OptionsPattern[]] := Module[{fullOpts,g,v,vs,i,c,wv,w,cw,ci,wi,paMatrix,weMatrix,imin,istop},
	fullOpts=Join[{opts},Options[findShortestCircle]];
	(* check if all weights are in the range of double values
	   and if not rescale all weights to double values
	   This is necessary because FindShortestPath does not work,
	   if the weights are outside the range of double *)
	wv = PropertyValue[gin,VertexWeight];
	(* even double value are not sufficient for this implementation of dijkstra :(
	   and can result in some strange artifacts... the condition below is somewhat handcrafted and wors ok..
	 *)
	(* If[ Max[wv] > $MaxMachineNumber || Min[wv] < $MinMachineNumber, *)
	If[ Min[wv] / Max[wv] < Exp[-100] && OptionValue[spMethod] == "fast" && ! OptionValue["clipWeights"], 
			g = rescaleWeightsToDouble[gin,FilterRules[fullOpts,Options[rescaleWeightsToDouble]]];
			,
			g = gin;
		];
	If[ OptionValue["clipWeights"],
		updateProperty[g,VertexWeight, Clip[PropertyValue[g,VertexWeight], {$MinMachineNumber,$MaxMachineNumber}]]; 
		updateProperty[g,EdgeWeight, Clip[PropertyValue[g,EdgeWeight], {$MinMachineNumber,$MaxMachineNumber}]]; 
	];
	(* Sort vertices by VertexWeight *)
	v = { g//VertexList, PropertyValue[g,VertexWeight] }//Transpose;
	v = SortBy[v,Second];
	paMatrix = pAngleArray[g,p];
	weMatrix = WeightedAdjacencyMatrix[g];
	(* loop over all vertices, which have a lower VertexWeight than the current minimal circle weight *)
	i = 1;
	c = {};
	w = Infinity;
	imin = i;
	istop = Min[v//Length, OptionValue[maxCheckedVertexes] ];
	If[ ! OptionValue[useParallel],
		While[ v[[i,2]] < w && i <= istop,
			(* find the shortest circle that contains the vertex v[[i,1]] *)
			{ci,wi} = findShortestCircle[g,p,v[[i,1]],paMatrix,weMatrix,opts];
			(* save circle if is shorter than the currently known shortest circle
			   in case there are two circles with the same weight we always use the one with less edges *)
			If[ wi < w || (wi == w && Length[ci] < Length[c]), (
				c = ci;
				w = wi;	
				imin = i;
				)
			];
			i += 1;
			(* dump memory usage to find memory leaks
			   sidenote: found memory leak was in
			   BreadthFirstScan *)
			If[OptionValue[SowMemoryInfo],
				Sow[{i,MemoryInUse[]}];
			];
		];
		, (* else *)
		vs = v[[1;;istop,1]];
		cw = ParallelMap[
			findShortestCircle[g,p,#,paMatrix,weMatrix,opts] &,
			vs,
			DistributedContexts -> {"CauchyIntegral`",$Context}
		];
		{c,w} = Sort[cw,#1[[2]] < #2[[2]] || (#1[[2]] == #2[[2]] && Length[#1//First] < Length[#2//First]) &]//First;
	];
	(* There can be duplicated edges in the "circle" near the source vertex from which the pathes 
  	for the circle were created if we don't check all vertexes.
	These can be removed without problems. *)
	If[ simplifyCircle//OptionValue,
		c = c //. {s_, t_, u__, t_, s_} :> {t, u, t};
	];
	(* update weight of the circle using the real weights and not the interally used weights *)
	weMatrix = WeightedAdjacencyMatrix[gin]; 
	w = weMatrix[[##]]& @@@ Partition[c,2,1]//Total;
	Return[{c,w}];
]
Options[findShortestCircle]=Join[
	{SowMemoryInfo->False,maxCheckedVertexes->Infinity,useParallel->False,simplifyCircle->True,spMethod->"fast",SowCircleValues->False,"clipWeights"->False},
	Options[rescaleWeightsToDouble]
	];

findShortestCircle[g_,p_,s_,paMatrix_,weMatrix_,opts:OptionsPattern[]] := Module[{palist,weightlist,circleValues,circleEdge,enclosingCircleValues,circle,splist,shortestCircle,temp},
	Switch[ OptionValue[spMethod],
		"fast",
		{splist,palist,weightlist} = fastFindShortestPath[g,s,All,paMatrix,weMatrix];
		,
		"precise",
		{splist,palist,weightlist} = preciseFindShortestPath[g,s,All,paMatrix,weMatrix];
		, 
		_,
		Abort[];
		
	];
	(* {splist,palist,weightlist} = fastFindShortestPath[g,s,All,paMatrix,weMatrix]; *)
	Sow[{splist,palist,weightlist}];
	
	circleValues = edgeMap[g,
		{#,
			weightlist[[#//First]] + weightlist[[#//Second]] + weMatrix[[#//First,#//Second]]
		  ,
		  	palist[[#//First]] - palist[[#//Second]] + paMatrix[[#//First,#//Second]]
		} &
	];
	(* Sow all found Circles ... maybe useful for debugging *)
	If[ OptionValue[SowCircleValues],
		Sow[circleValues]
	];
	(* Select just pathes that really enclose p *)
	enclosingCircleValues = Select[circleValues, Abs[ #[[3]] ] > (2Pi - 0.1) &];
	(* Select the circle with minimum weight and in case there is more than one, we select the one
	   which has the lowest amount of edges*)
	shortestCircle = Sort[enclosingCircleValues, 
		#1[[2]] < #2[[2]] 
		|| 
		( 
		  #1[[2]] == #2[[2]] 
		  &&
		  (* Length[ ...] = number of edges in the path *) 
		  Length[splist[[ List@@First[#1] ]]//Flatten] < Length[splist[[ List@@First[#2] ]]//Flatten]
		) & ] //First;
	circleEdge = shortestCircle//First;
	(* create final circle *)
	circle = Join[ 
				splist[[circleEdge//First]],
				splist[[circleEdge//Second]]//Reverse 
			]; 	
	(* make sure the circles will always be traversed in the same direction *)
	If[ shortestCircle[[3]] < 0,
		circle = Reverse[circle];
	];
	Return[{circle,shortestCircle//Second}];
]
SetAttributes[findShortestCircle,HoldFirst];

	
(* converts the outer angle of a triangle to an inner angle *)
toInnerAngle[a_] := a
toInnerAngle[a_?(# > Pi &)] := a - 2Pi;
toInnerAngle[a_?(# < -Pi &)] := 2Pi + a;

addpAngle[g_,p_] := 
	edgeMap[g,
		(PropertyValue[{g,#},"pAngle"] = toInnerAngle @ First @ Differences @ Arg[ complexCoordinates[g,#] - p] ) &
	];
SetAttributes[addpAngle,HoldFirst];

circlePath[g_Graph,e:_DirectedEdge|_UndirectedEdge,s_] := 
	Join[ FindShortestPath[g,s,e//First],FindShortestPath[g,e//Second,s] ];

(* maybe this can be done in a faster way without using //DirectedGraph
   Problem:
   without //DirectedGraph, the resulting matrix is not necessarrily quadratic
   so the easy solution result = m - Transpose[m] does not work
*)
pAngleArray[g_Graph,p_] := Module[{gd,cv,res},
	gd = g//DirectedGraph;
	cv = complexCoordinates[g];
	res = edgeMap[gd,
		List @@ # -> toInnerAngle @ First @ Differences @ Arg[ cv[[List@@#]] - p] &
	]//SparseArray;
	Return[res];
]

fastFindShortestPath[g_Graph,s_,All] :=  Module[{spfunction, spg, splist},
  (* create ShortestPathFunction for pathes from s to any other point *)
  spfunction = FindShortestPath[g, s, All];
  (* spfunction[[2,4,1]] contains a SparseArray that encodes the minimal spannig tree for this problem *)
  (* WARNING
	using the option 
		DirectedEdges->False
	is about 1000x slower than omiting it and using the UndirectedGraph function afterwards
  *)
  spg = AdjacencyGraph[ spfunction[[2, 4, 1]] ] // UndirectedGraph;
  (* build shortest pathes with bfs *)
  splist = ConstantArray[{}, g // VertexCount];
  BreadthFirstScan[spg, s,
   {
   	"DiscoverVertex" -> (
      (splist[[#1]] = Append[splist[[#2]], #1]); &
      )
    }
   ];
  Return[splist];
];

fastFindShortestPath[g_Graph,s_,All,paMatrix_,weMatrix_] :=  Module[{spfunction, spg, splist,palist,weightlist},
  (* create ShortestPathFunction for pathes from s to any other point *)
  spfunction = FindShortestPath[g, s, All];
  (* spfunction[[2,4,1]] contains a SparseArray that encodes the minimal spannig tree for this problem *)
  (* WARNING
	using the option 
		DirectedEdges->False
	is about 1000x slower than omiting it and using the UndirectedGraph function afterwards
  *)
  spg = AdjacencyGraph[ spfunction[[2, 4, 1]] ] // UndirectedGraph;
  (* build shortest pathes with bfs *)
  palist = ConstantArray[0, g // VertexCount];
  weightlist = ConstantArray[0, g // VertexCount];
  splist = ConstantArray[{}, g // VertexCount];
  DepthFirstScan[spg, s,
   {
   	"DiscoverVertex" -> (
	      (
	      splist[[#1]] = Append[splist[[#2]], #1];
	      palist[[#1]] = palist[[#2]] + paMatrix[[#2,#1]];
	      weightlist[[#1]] += weightlist[[#2]] + weMatrix[[#2,#1]];
	      ) &
      )
    }
   ];
  Return[{splist,palist,weightlist}];
];

preciseFindShortestPath[g_Graph,s_,All,paMatrix_,weMatrix_] := Module[{palist,weightlist,splist,neighbours,sel,v,vn,i,vmin,wmin,vsel,distlist},
  (* calculate all neighbours of all vertexes *)
  neighbours = ConstantArray[{},g//VertexCount];
  DepthFirstScan[g, s,
   {
   	"DiscoverVertex" -> (
	      (
	      neighbours[[#2]] = Append[neighbours[[#2]],#1];
	      ) &
      )
      ,
     "UnvisitedVertex" -> (
     	(
	      neighbours[[#2]] = Append[neighbours[[#2]],#1];
    	)&
     )
     ,
     "VisitedVertex" -> (
     	(
	      neighbours[[#2]] = Append[neighbours[[#2]],#1];
     	)&
     )
    }
   ];
  (* datastructure setup *)
  (* - angles *)
  palist = ConstantArray[0, g // VertexCount];
  (* weights being Inf except at s *)
  weightlist = ConstantArray[Infinity, g // VertexCount];
  weightlist[[s]] = 0;
  distlist = ConstantArray[Infinity,g //VertexCount];
  distlist[[s]] = 0;
  (* shortest pathes *)
  splist = ConstantArray[{}, g // VertexCount];
  splist[[s]] = {s};
  (* unprocessed vertexes *)
  sel = ConstantArray[True,g//VertexCount];
  sel[[s]] = False;
  v = s;
  vn = g//VertexCount;
  For[ i=1, i < vn, i++,
  	(* update weights,pathes and angles *)
  	( If[ weightlist[[#]] > weightlist[[v]] + weMatrix[[v, #]] || (weightlist[[#]] == weightlist[[v]] + weMatrix[[v,#]] && distlist[[#]] > distlist[[v]]+1),
  		weightlist[[#]] = weightlist[[v]] + weMatrix[[v,#]];
  		distlist[[#]] = distlist[[v]] + 1;
  		splist[[#]] = Append[splist[[v]],#];
  		palist[[#]] = palist[[v]] + paMatrix[[v,#]];
  	]; ) & /@ neighbours[[v]]; 
  	
  	(* find unprosessed vertex with minimal weight *)
  	wmin = Min[Pick[weightlist,sel]];
  	vmin = Position[weightlist,wmin] //Flatten;
  	vsel = Position[sel[[vmin]],True];
  	(* vsel = Position[sel[[vmin]],True]//First//First;*)
  	(* and minimial distance if there is a tie *)
  	vsel = If[ Length[vsel] > 1,
  		First@SortBy[vsel,distlist[[First@#]]&]
  		,
  		vsel//First//First	
  	];
  	vmin = vmin[[vsel]];
    (* remove vertex from eligable new vertexes *)
  	sel[[vmin]] = False;
  	(* set new vertex *)
  	v = vmin;
  ];
  Return[{splist,palist,weightlist}];
]
	

contourCauchyIntegral[g_Graph,p_,f_,n_,opts:OptionsPattern[]] := Module[{fullOpts,fint,parts,z,prevInt,curInt,prevPts,curPts,prevErr,curErr,rp,active,converging,tint,activePos,i,dupPts,zPts,minErr},
	fullOpts=Join[{opts},Options[contourCauchyIntegral]];
	(* create integrant *)
	fint = Evaluate[f[#] #^(-n-1)]&;
	(* get coordinates of relevant edges *)
	parts = relevantContourParts[g,p,FilterRules[fullOpts,Options[relevantContourParts]]]; 
	z = Partition[complexCoordinates[g,#],2,1] &/@ parts;
	(* simplify contour *)
	If[ OptionValue[simplifyContour],
		(* combine adjacent intervals with same direction *)
		z = z //. {s___, {a_, b_}, {c_, d_}, r___} /; relErr[Normalize[b - a], Normalize[d - c]] < -12 :> {s, {a, d}, r};
	];
	(* number of duplicate points in the contour - used later to correct the total number of nodes *)
	dupPts = Total[Length[#]-2 & /@ z];
	(* correct precision of coordinates *)
	z = SetPrecision[z,OptionValue@WorkingPrecision];
	z = Flatten[z,1];
	rp = OptionValue[rulePoints];
	(* initial integration along edges *)
	curInt = linearPathNIntegrate[fint,z,FilterRules[fullOpts,Options[linearPathNIntegrate]]]; 
	(* force precision to max, as otherwise the iteration could stop early because mathematica
	   thinks the result has a lower precision than it acutally has *)
	curInt = SetPrecision[curInt,OptionValue@WorkingPrecision];
	curPts = ConstantArray[2 rp - 1,Length[z]];
	zPts = ConstantArray[ First@NIntegrate`ClenshawCurtisRuleData[rp,OptionValue@WorkingPrecision], Length[z]];
	(* reduce precision as this makes it easier later on find identical nodes and remove them*)	
	zPts = SetPrecision[ zPts, OptionValue@WorkingPrecision -2];
	curErr = ConstantArray[Infinity,Length[z]];
	(* smallest error so far for an interval *)
	minErr = ConstantArray[Infinity,Length[z]];
	tint = Total[curInt];
	(* dump intermediate results *)
	Sow[{1/(2 Pi I) tint,Total@curPts - dupPts}];
	(* set status of all edges to active, as we can't assume the integral has already converged *)
	active = ConstantArray[True,Length[z]];
	activePos = Flatten@Position[active,True];
	(* increate number of rule points for all active edges until the integral converges *)
	i = 0;
	While[ activePos =!= {} && i < OptionValue@MaxIterations ,
		i++;
		(* if nested is specified rp is increased in a way
		   that allows previous evaluations of f to be reused*)
		If[OptionValue[iterationStepSize] == "nested",
			rp = 2 rp - 1;
			,	
			rp = rp + OptionValue[iterationStepSize];
		];
		(* store old values *)
		prevInt = curInt;
		prevPts = curPts;
		prevErr = curErr;
		(* integrate active edges with increased number of rule points *)
		curInt[[activePos]] = linearPathNIntegrate[fint,z[[activePos]],rulePoints->rp,FilterRules[fullOpts, Options[linearPathNIntegrate]]]; 
		curInt = SetPrecision[curInt,OptionValue@WorkingPrecision];
		curErr[[activePos]] = MapThread[relErr,{prevInt[[activePos]],curInt[[activePos]]}];
		minErr[[activePos]] = MapThread[Min,{curErr[[activePos]],minErr[[activePos]]}];
		(* create sum over all nodes used so far or just the numer of nodes in the current iteration step *)
		If[ OptionValue@cumulativeNodeCount,
			zPts[[activePos]] = Union[
									#,
									SetPrecision[
										First@NIntegrate`ClenshawCurtisRuleData[rp,OptionValue@WorkingPrecision],
										OptionValue[WorkingPrecision] -2
									]
								] & /@ zPts[[activePos]];
			curPts[[activePos]] = Length /@ zPts[[activePos]];
			,
			curPts[[activePos]] = 2 rp - 1;
		];
		(* Debug
		Print[
			Show[
				Graphics[{Black,Thick,Line[{{Re@#1, Im@#1}, {Re@#2, Im@#2}}] & @@@ z}],
				Graphics[{Red,Thick,Line[{{Re@#1, Im@#1}, {Re@#2, Im@#2}}] & @@@ z[[activePos]]}]
			]
		]; *)
		tint = SetPrecision[Total[curInt],OptionValue@WorkingPrecision];
		(* determine on which edges the integral has not yet converged *)
		active = (curErr + Log10@Abs[curInt/tint]) > -OptionValue[WorkingPrecision] //Thread;
		(* or are unlikely to converge further *)
		(* setting the precision of curErr is necessary as > might yield undesired results if the precision is too low *)
		curErr = SetPrecision[curErr,OptionValue@WorkingPrecision];
		If[ OptionValue@convergenceTest,
			converging = Thread@ !Thread[ Thread[curErr < -OptionValue[PrecisionGoal]/2] && Thread[minErr+0.5 < curErr] ];
			active = Thread[active && converging];
		];
		activePos = Flatten@Position[active,True];
		(* dump intermediate results *)
		Sow[{1/(2 Pi I) tint, Total@curPts - dupPts}];
		If[ Position[active,Except[True|False],{1},Heads->False] =!= {},
			(* NOTE: Except[True|False] does not work for Pick *)
			Sow[Pick[curInt/tint,active,_ > -MachinePrecision]];
			Sow[Pick[Transpose@{prevInt,curInt},active,_ > -MachinePrecision]];
		];
	];
	If[i == OptionValue@MaxIterations,
		Message[contourCauchyIntegral::maxIter,OptionValue@MaxIterations];
	];
	Return[1/(2 Pi I) Total@curInt];
];
Options[contourCauchyIntegral] := Join[
									{simplifyContour->True,MaxIterations->100,iterationStepSize->1,cumulativeNodeCount->False,convergenceTest->True},
									{rulePoints->2,bufferPrecision->2},
									Options[linearPathNIntegrate],
									Options[relevantContourParts]
								];			

integralConvergenceData[g_Graph,p_,f_,n_,opts:OptionsPattern[]] := Module[{ref,fullOpts,int,convData,err},
	fullOpts=Join[{opts},Options[contourCauchyIntegral]];
	(* calculate reference solution with increased precision *) 
	ref = pathCauchyIntegral[g, p, f, n, WorkingPrecision -> OptionValue[WorkingPrecision] + MachinePrecision,
										 PrecisionGoal -> OptionValue[WorkingPrecision],
										 FilterRules[fullOpts,Options[pathCauchyIntegral]]];
	(* reduce precision of ref, as otherwise relErr can return Indeterminate *)
	ref = SetPrecision[ref,OptionValue@WorkingPrecision]; 
	(* calculate convergence data *) 
	If[OptionValue[fixPrecision],	
		Block[{$MaxExtraPrecision=0,$MaxPrecision= OptionValue[WorkingPrecision]},
			{int,{convData}} = Reap[contourCauchyIntegral[g, p, f, n,FilterRules[fullOpts,Options[contourCauchyIntegral]]]];
		 ];
	 ,
		{int,{convData}} = Reap[contourCauchyIntegral[g, p, f, n,FilterRules[fullOpts,Options[contourCauchyIntegral]]]];
	];
	err = relErr[#,ref] &/@ convData[[All,1]];
	Return[{convData[[All,2]],err}];
];
Options[integralConvergenceData] = Join[
								{fixPrecision->True},
								Options[contourCauchyIntegral],
								Options[pathCauchyIntegral]
								];

(* remove parts of a graph crossing or on a line (useful for removing branch cuts) *)
removeIntersectingParts[g_,Line[{a_,b_}]] := Module[{cv,alpha,dv,gout,deIndex,de,testIn01,A,R},
	cv = complexCoordinates[g];	
	testIn01 = Function[{u},Re[u] > 0 && Re[u] < 1 && Abs@Im[u] < 10^-14,Listable] ;
	(* remove vertexes first *)
	alpha = (cv - a)/(b - a);
	dv = Select[ g//VertexList, testIn01[alpha[[#]]] &];
	gout = VertexDelete[g,dv];
	(* remove edges afterwards *)
	A = { Re[ {b-a, cv[[#1]] - cv[[#2]]} ],
		  Im[ {b-a, cv[[#1]] - cv[[#2]]} ]} &@@@ List@@@EdgeList[gout];
	R = { Re[cv[[#1]] - a], Im[ cv[[#1]] - a] }  &@@@ List@@@EdgeList[gout];
	(* alpha contains the parameters to calculate the intersecting point (which are Infinity, if the lines are parallel) *)
	alpha = If[ Abs@Det[A[[#]]] > 10^-8 ,
				LinearSolve[A[[#]],R[[#]]],
				{Infinity,Infinity}
			] & /@ Range@EdgeCount[gout];
	deIndex = Select[Range@EdgeCount[gout],And@@testIn01[alpha[[#]]] & ];
	de = EdgeList[gout][[deIndex]];
	gout = EdgeDelete[gout,de];
	(* finally convert the graph back to an indexed graph *)
	gout = IndexGraph[gout];
	Return[gout];
]
removeIntersectingParts[g_,l_List] := Fold[removeIntersectingParts,g,l];

shortestPathForCauchyInt[f_,n_,d_,nodes_,opts:OptionsPattern[]] := Module[{g,gf,v0,circleData,fullOpts,xEdges},
	(* build array will all options *)
	fullOpts = Join[{opts},Options[shortestPathForCauchyInt]];
	(* create a grid over the square
	   {{-d,d},{-d,d}}
	   and use the absolute value of the function f over this grid 
	   as weight for the graph
	   *)
	If[ OptionValue[xGrid],
		g = xGridGraph[{nodes,nodes}];
		,
		g = GridGraph[{nodes,nodes}];
	];
	fixVertexCoordinates[g];
	rescale[g,{{-d,d},{-d,d}}];
	(* if a vertex is to close to 0, we drop it, as evaluating gf at 0 causes problems *)
	v0 = closestVertice[g,0];
	If[ Abs@complexCoordinates[g,v0] < d/nodes/10,
		g = IndexGraph@VertexDelete[g,v0];
	];
	(* remove vertex on a branchcut and edges across a branch cut *)
	If[ OptionValue[branchCut] =!= Null,
	    g = removeIntersectingParts[g,OptionValue[branchCut]];	
	];
	gf = Function[{z},f[z]/z^(n+1) //Abs];
	addVertexEdgeWeight[g,gf,FilterRules[fullOpts,Options[addVertexEdgeWeight]]];	
	PropertyValue[g,"VertexWeightFunction"] = Function[gf[#]//Evaluate];
	
	circleData = findShortestCircle[g,0,FilterRules[fullOpts,Options[findShortestCircle]]];
	Return[Prepend[circleData,g]];
];
Options[shortestPathForCauchyInt] = Join[{WorkingPrecision->MachinePrecision,
										  maxCheckedVertexes->1,Method->"TrapezoidalRule",rulePoints->1,
										  branchCut->Null, xGrid->True },
										  Options[findShortestCircle],
										  Options[addVertexEdgeWeight] ];

shortestPathForCauchyIntIterate[f_,n_,nodes_,opts:OptionsPattern[]] := Module[{fullOpts,spfciOpts,gCur,gPrev,circleCur,circlePrev,wCur,wPrev,d,i},
	(* build array will all options *)
	fullOpts = Join[{opts},Options@shortestPathForCauchyIntIterate];
	spfciOpts = FilterRules[fullOpts,Options@shortestPathForCauchyInt];
	wPrev = Infinity;
	wCur  = 0;
	d = OptionValue["InitialGridRadius"];
	i = 1;
	(* increase region covered by the graph until the weight does not decrease anymore *)
	{gCur,circleCur,wCur} = shortestPathForCauchyInt[f,n,d,nodes,spfciOpts];
	(* TODO: this is not really perfectly stable .. as the grid gets more coarse, it will also change the weight... *)
	While[ wCur < wPrev && d < OptionValue@"MaxGridRadius",
		d = 2 d;
		i = i + 1;
		{gPrev,circlePrev,wPrev} = {gCur,circleCur,wCur};
		{gCur,circleCur,wCur} = shortestPathForCauchyInt[f,n,d,nodes,spfciOpts];
	];	
	(* return the better circle of the last two that have been calculated *)
	If[ wPrev < Infinity && wCur > wPrev,
		Return[{gPrev,circlePrev,wPrev}];
		,
		Return[{gCur,circleCur,wCur}];
	]
]
Options[shortestPathForCauchyIntIterate] = Join[{"MaxGridRadius" -> 1024,"InitialGridRadius"->1}, Options[shortestPathForCauchyInt]];

CauchyIntegralSEW[f_,n_,z_,opts:OptionsPattern[]] := Module[{fs,g,sew,weight,fullOpts,bcs},
	fullOpts = Join[{opts},Options[CauchyIntegralD]];
	(* shift the input function by z as the the main part of the algorithm has been implemented for z=0 *)
	fs = f[#+z] &;
	(* correspondingly we shift branch-cuts by -z *)
	bcs = OptionValue["Cuts"] /. x_?NumericQ :> x - z; 
	(* calculate SEW *)
	{g,sew,weight} = shortestPathForCauchyIntIterate[fs,n,OptionValue@"GridSize",branchCut->bcs,FilterRules[fullOpts,Options@shortestPathForCauchyIntIterate]];
	Return[{g,sew}];
];
Options[CauchyIntegralSEW] = Join[ {"GridSize"->51,"Cuts"->Null},Options[shortestPathForCauchyIntIterate]];

CauchyIntegral[g_,sew_,f_,n_,z_,opts:OptionsPattern[]] := Module[{dfz,fs},
	(* shift the input function by z as the the main part of the algorithm has been implemented for z=0 *)
	fs = f[#+z] &;
	(* evaluate cauchy integral *)
	dfz = n! contourCauchyIntegral[g,sew,fs,n,useParallel->False,FilterRules[{opts},Options@contourCauchyIntegral]];
	Return[dfz];
]; 
Options[CauchyIntegral] = Join[{WorkingPrecision->MachinePrecision,PrecisionGoal->MachinePrecision,MaxIterations->100}];

CauchyIntegralD[f_,n_,z_,opts:OptionsPattern[]] := Module[{g,sew,fullOpts,dfz},
	fullOpts = Join[{opts},Options[CauchyIntegralD]];
	(* calculate SEW *)
	{g,sew} = CauchyIntegralSEW[f,n,z,FilterRules[fullOpts,Options@CauchyIntegralSEW]];
	(* evaluate cauchy integral *)
	dfz = CauchyIntegral[g,sew,f,n,z];
	Return[dfz];
];
Options[CauchyIntegralD] = Options[CauchyIntegralSEW];

SEWContourPlot[g_,sew_] := Show[
	vertexWeightLogContourPlot[g,sew],
	pathPlot[g,sew]
];
	

(* remove unimportant parts of a circle *)
relevantContourParts[g_Graph,c_,opts:OptionsPattern[]] := Module[{we,wc,ec,parts,i,part,mw,min,ein,mode},
		we = WeightedAdjacencyMatrix[g];
		(* create vector with edges and their weight *)
		ec = Partition[c,2,1]; 
		wc = Part[we,##] &@@@ ec;
		mw = Max[wc];
		(* calculate minimum weight of an edge to be considered relevant *)
		min = mw / 10^(OptionValue[PrecisionGoal] + OptionValue[bufferPrecision]);
		ein = Thread[wc > min]; 
		(* mode: 0 -> currently in a relevant part, 1 -> currently outside a relevant part *)
		mode = 1; 
		parts = {};
		part = {};
		For[i=1,i<=Length[ein],i=i+1,
			If[ ein[[i]],
				(* weight is above threshold, so we add it to the current part *)
				part = Append[part,ec[[i]]];
				mode = 0;
				,
				If[ mode == 0,
					(* weight of current edge is below threshold, but last edge was added to part*)
					If[ Or @@ ein[[ Mod[i + Range@OptionValue[lookAhead],Length[ein],1] ]],
						(* one of the next "lookAhead" edges is above the threshold so we will also add this edge *)
						part = Append[part,ec[[i]]];
						,
						(* start a new part as the last one just ended *)
						parts = Append[parts, Join@@part //. {s___,a_,a_,r___} :> {s,a,r}];
						part = {};
						mode = 1;
					]
				];
			];
		];
		(* append last part if it has been done already *)
		If[ mode == 0,
			parts = Append[parts,Join@@part //. {s___,a_,a_,r___} :> {s,a,r}];
		];
		Return[parts];
];
Options[relevantContourParts] = {PrecisionGoal->MachinePrecision,bufferPrecision->8,lookAhead->1};

(* refine the circle c in the graph g *)
refineShortestCircle[g_Graph,c_,opts:OptionsPattern[]] := Module[{bg,cn,fullOpts},
	(* build array with all options *)
	fullOpts = Join[{opts},Options[refineShortestCircle]];
	(* create a band around the circle *)
	bg = bandGridGraph[g, c, FilterRules[{fullOpts},Options[bandGridGraph]]];
	(* remove branchCuts *)
	If[ OptionValue[branchCut] =!= Null,
		Print["branch"];
	    bg = removeIntersectingParts[bg,OptionValue[branchCut]];	
	];
	(* find the shortest circle in this band *)
	cn = findShortestCircle[bg,0,FilterRules[{fullOpts},Options[findShortestCircle]] ];
	Return[Prepend[cn,bg]];
]; 
Options[refineShortestCircle] = Join[{maxCheckedVertexes->1,branchCut->Null}, Options[findShortestCircle],Options[bandGridGraph]];

bandGridGraph[g_Graph,c_,opts:OptionsPattern[]] := Module[{n,k,dx,dy,gtemp,gh,gv,ev,vc,v1,v2,b,i,vertexes,edges,coordinates,sortedVertexes,vertexGrp,vertexRename,gb,wf,fullOpts},
	fullOpts = Join[{opts},Options[bandGridGraph]];
	(* create base graphs, which will later be mapped onto
	   2 rectangles in the original grid
	   hg => horizontal, vg => vertical *)
	n = OptionValue[subDivisions];
	k = OptionValue[maxDistanceFromCircle];
	gh = GridGraph[{k 2n+1,n+1}];
	gv = GridGraph[{n+1,k 2n+1}];
	vc = gh //VertexCount;
	(* determine deltas in the GridGraph g in x and y direction *)
	{dx,dy} = gridDeltas[g];
	{vertexes,edges,coordinates} = {{},{},{}};
	For[i = 1, i < Length[c], i++,
		v1 = c[[i]];
		v2 = c[[i+1]];
		ev = edgeVector[g,UndirectedEdge[v1,v2]];
		b = PropertyValue[{g,v2},VertexCoordinates];
		If[ Abs@ev[[1]] > Abs@ev[[2]],
			gtemp = IndexGraph[gh,(i-1)vc + 1];
			rescale[gtemp,{b + {0,k dy},b - {0,k dy} + ev}//Transpose];
		];	
		If[ Abs@ev[[1]] < Abs@ev[[2]],
			gtemp = IndexGraph[gv,(i-1)vc + 1];
			rescale[gtemp,{b + {k dx,0},b - {k dx,0} + ev}//Transpose];
		];	
		If[ Abs@ev[[1]] == Abs@ev[[2]],
			Print["error:"];
			Print[ev];
		];
		vertexes = Join[vertexes,gtemp //VertexList];
		edges = Join[edges,gtemp //EdgeList];
		coordinates = Join[coordinates,PropertyValue[gtemp,VertexCoordinates]];
	];
	(* determine groups of vertexes which are located at the same location*)
	(* sorting the vertexes by their coordinates and splitting the sorted array into groups is faster and scales better than using gather *)
	sortedVertexes = Sort[vertexes, 
			With[{c1=coordinates[[#1]],c2=coordinates[[#2]]},
				 ( (Abs[ c1[[1]] - c2[[1]] ] < Abs[ dx / n ] / 2  ) && c1[[2]] < c2[[2]] ) 
				 ||
				 ( (Abs[ c1[[1]] - c2[[1]] ] >= Abs[ dx / n ] / 2  ) && c1[[1]] < c2[[1]] )
			]&
	];
	vertexGrp = Split[sortedVertexes, coordinates[[#1]] == coordinates[[#2]] || relErr[coordinates[[#1]],coordinates[[#2]]] < -13 &];
	(* reducing the precision will cause == to also yield true when two vertexes are located very close to each other
	   this is a lot fast than checking if two points are very close to each other inside of gather *)
	(*
	lowpreCoordinates = SetPrecision[coordinates,MachinePrecision/2];
	vertexGrp = Gather[vertexes, lowpreCoordinates[[#1]] == lowpreCoordinates[[#2]]  &];
	*)
	(*
	vertexGrp = Gather[vertexes, coordinates[[#1]] == coordinates[[#2]] || relErr[coordinates[[#1]], coordinates[[#2]]] < -14 &];
	*)
	(* the vertexes in each group are merged in to one vertex, which is given the name of the first vertex in the group *)
	vertexes = vertexGrp[[All,1]];
	vertexGrp = Select[vertexGrp,Length[#] > 1 &]; 
	vertexRename = Thread /@ Thread @ Rule[vertexGrp[[All,2;;-1]], vertexGrp[[All,1]] ];
	vertexRename = Flatten[vertexRename];
	(* remove edges that are actually the same *)
	(* Sort vertexes in edges as this makes it much faster to remove duplicates afterwards instead of
	   using DeleteDuplicates[ ... , sameEdgeQ] which takes forever *)
	edges = edges /. vertexRename;
	edges = Sort /@ edges;
	edges = DeleteDuplicates[edges];
	coordinates = coordinates[[vertexes]];
	(* correct the vertexnames to make the final graph an IndexGraph *)
	vertexRename = Thread @ Rule[ vertexes, Range[ vertexes//Length ] ];
	edges = edges /. vertexRename;
	vertexes = Range[ vertexes//Length ];
	gb = Graph[vertexes,edges,VertexCoordinates->coordinates];
	(* add Weights *)
	wf = PropertyValue[g,"VertexWeightFunction"];
	If[ wf =!= $Failed,
		(*addEdgeWeightByVertexWf[gb,wf];*)
		addVertexEdgeWeight[gb,wf,FilterRules[fullOpts,Options[addVertexEdgeWeight]]];	
		PropertyValue[gb,"VertexWeightFunction"] = wf;
	];
	Return[ gb ];
];
Options[bandGridGraph] = Join[{WorkingPrecision->MachinePrecision, subDivisions -> 2, maxDistanceFromCircle -> 1},
							   Options[addVertexEdgeWeight]
							];

gridDeltas[g_Graph] := Module[{v0,e0,deltas},
	v0 = g//VertexList//First;
	e0 = incidentEdges[g,v0];
	(* vectors in opposite directions are removed in case there are any *)
	deltas = Total @ DeleteDuplicates[
		edgeVector[g,e0,v0],
		-#1 == #2 || relErr[#1,-#2] < -8 &
	];
	Return[ Abs/@ deltas];
]

End[]

