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
edgeVector::wrongEdge="Can't use Vertex `1` as starting point of vector as Edge `2` does not contain it"

Begin["`Private`"]
(* creates {vl, vr} for all edges in e *)
extractEdges[g_Graph] := 
	Map[
		PropertyValue[{g,#},VertexCoordinates] &
		, 
		List @@@ EdgeList[g]    (* List @@@ changes Head from UndirectedEdge to List *)
		,
		{2}
	];

vertexMap[g_Graph,f_] := f[#] & /@ VertexList[g];

edgeMap[g_Graph,f_] := f[#] & /@ EdgeList[g];

(* 
threaded MinMax calculates the Min and Max of all innermost Lists
Level -2 of m has to be something like {a,b,c} *)
threadedMinMax[m_] := Apply[{Min[##], Max[##]} &, m, {-2}];

(* rescale VertexCoordinates of the Graph g from the range nr to the
 range or and return the these rescaled coordinates*)
rescaledCoordinates[g_,nr_,or_] := Transpose @ MapThread[
	Rescale,
	{ Transpose@PropertyValue[g,VertexCoordinates],
	  or,
	  nr
	}
]
SetAttributes[rescaledCoordinates,HoldFirst];

rescale[g_,nr_,or_] := Module[{vc,v},
	 vc = rescaledCoordinates[g,nr,or];
	 If[ $VersionNumber >= 10,
	 	 updateProperty[g,VertexCoordinates,vc];
	 	 ,
         v = VertexList[g];
         (*BUG in 8.0.4:
           Changing the VertexCoordinates Property of a graph ist NOT possible. 
           One can only change the VertexCoordinates of a single Vertex*)
         (PropertyValue[{g,v[[#]]},VertexCoordinates] = vc[[#]]) &/@ Range[v//Length];
	 ];
	 Return[g];
]

rescale[g_,nr_] := With[{or=threadedMinMax@Transpose@PropertyValue[g,VertexCoordinates]},
	rescale[g,nr,or]	
]
SetAttributes[rescale,HoldFirst];


(* add VertexWeight given by the function f to the Graph g, so that VertexWeight[v] = f[v] for all vetrices v*)
(* this defintion of addVertexWeuight will NOT work in Mathematica 8.0.0 due to a bug in the Graph API
   ... oh and this usage of the PropertyValue function is also undocumented *) 
addVertexWeight[g_, f_,pre_:MachinePrecision] := updateProperty[g,VertexWeight, vertexMap[g, f @ complexCoordinates[g,#,pre] & ]];
SetAttributes[addVertexWeight,HoldFirst];
  
(* this defintion of addEdgeweight will NOT work in Mathematica 8.0.0 due to a bug in the Graph API
   ... oh and this usage of the PropertyValue function is also undocumented *) 
addEdgeWeight[g_, f_] := updateProperty[g,EdgeWeight, edgeMap[g, f[g,#] & ]];

addEdgeWeight[g_, we_List] := PropertyValue[g,EdgeWeight] = we;
 
(* HoldFirst is necessary as PropertyValue needs the 
    actual Symbol of the Graph *)
SetAttributes[addEdgeWeight,HoldFirst];
  
addEdgeWeightByVertexWf[g_,f_,pre_:MachinePrecision] := Block[{},
  addEdgeWeight[g,Mean @ Thread @ f @ complexCoordinates[##,pre]&];
  addVertexWeight[g,f,pre];
];
SetAttributes[addEdgeWeightByVertexWf,HoldFirst];

addVertexEdgeWeightTrapezoidal[g_,f_,opts:OptionsPattern[]] := Module[{cv,e,wv,we},
	cv = SetPrecision[complexCoordinates[g],OptionValue[WorkingPrecision]];
	e = List @@@ EdgeList[g];
	(* evaluate vertexWeight *)
	wv = Quiet[f /@ cv /. Infinity -> $MaxMachineNumber/10];
	(* calculate corresponding EdgeWeight given by TrapezoidalRule *)
	we = Abs@Differences[ cv[[#]] ] * Mean[wv[[#]]] &/@e;
	(* set weights *)
	PropertyValue[g,VertexWeight] = wv;
	PropertyValue[g,EdgeWeight] = we[[All,1]];
];
SetAttributes[addVertexEdgeWeightTrapezoidal,HoldFirst];
Options[addVertexEdgeWeightTrapezoidal] = {WorkingPrecision->MachinePrecision};

addVertexEdgeWeight[g_,f_,opts:OptionsPattern[]] := Module[{fullOpts},
  fullOpts=Join[{opts},Options[addVertexWeight]];
  If[OptionValue[Method] == "TrapezoidalRule" && OptionValue[rulePoints] == 1,
  	  (* special faster version for this case *)
  	  addVertexEdgeWeightTrapezoidal[g,f,FilterRules[fullOpts,Options[addVertexEdgeWeightTrapezoidal]]];
  	,
	  addEdgeWeight[g, edgeNIntegrate[g,f,g//EdgeList,FilterRules[fullOpts,Options[edgeNIntegrate]]]];
	  addVertexWeight[g,f,WorkingPrecision//OptionValue];
  ]
]
SetAttributes[addVertexEdgeWeight,HoldFirst];
Options[addVertexEdgeWeight] := Join[{postProcessFunction->Abs},Options[edgeNIntegrate]];

(* get the coordinates of the vertices in the edge e in the complex plane *)
complexCoordinates[g_Graph,(e_UndirectedEdge|e_DirectedEdge)] :=
	Complex @@ PropertyValue[{g,#},VertexCoordinates] &/@ ( List @@ e )
(* get the coordinates of the vertice v in the complex plane *) 
complexCoordinates[g_Graph,v_] :=
	Complex @@ PropertyValue[{g,v},VertexCoordinates] 
complexCoordinates[g_Graph,v_List] :=
	Complex @@@ listPropertyValue[g,VertexCoordinates,v] 
complexCoordinates[g_Graph] :=
	Complex @@@ PropertyValue[g,VertexCoordinates];

(* get the coordinates of a vertex / edge with a given precision *)
complexCoordinates[g_Graph,voe_,pre_] :=
	SetPrecision[
		complexCoordinates[g,voe]
		,
		pre
	];

(* return all neighbours of v in g *)
neighbours[g_Graph,v_] := incidentEdges[g,v] /. _[n_|v,v|n_] :> n; 

(* returns a list of all edges incident to v *)
incidentEdges[g_Graph,v_] := EdgeList[g, _[v,_] | _[_,v] ];

edgePattern = _DirectedEdge | _UndirectedEdge;

(* vector coressponding to the edge e *)
edgeVector[g_Graph,e:edgePattern] := Flatten[
	vertexPropertyValue[g,VertexCoordinates,e] //Differences
	,
	2
]
	 
(* vector corresponding to the edge e starting at v *)
edgeVector[g_Graph,e:edgePattern,v_] := If[e[[1]] == v,
	edgeVector[g,e]
	,
	If[e[[2]] == v,
		edgeVector[g,e//Reverse]
		,
		Message[edgeVector::wrongEdge,v,e];
	]
];
	
SetAttributes[edgeVector,Listable];



(* get the PropertyValue of the property p at the endpoints of an edge *)
vertexPropertyValue[g_Graph,p_,e:_UndirectedEdge|_DirectedEdge] := listPropertyValue[g,p,List@@e] 

(* converts a path given by a list of Vertices to a List of undirected edges *)
pathToEdges[p_] := UndirectedEdge[Most[p], Rest[p]] //Thread;
pathToDirectedEdges[p_] := DirectedEdge[Most[p], Rest[p]] //Thread;

pathEdgeWeight[g_Graph, p_] := pathEdgeWeight[g,pathToEdges[p]];

pathEdgeWeight[g_Graph, e:{(_UndirectedEdge|_DirectedEdge)..}] :=
  PropertyValue[{g,#},EdgeWeight] &/@ e //Total

(* copy all properties belonging to part from the Graph source to the Graph target *)
copyGraphProperties[target_,source_,part_] :=
	(PropertyValue[{target,part},#] = PropertyValue[{source,part},#]) &/@ PropertyList[{source,part}];

(* copy all properties belonging to edgees or vertexes from the Graph source to the Graph target *)
copyGraphProperties[target_,source_] := Block[{},
	vertexMap[target,copyGraphProperties[target,source,#]&]; 
	edgeMap[target,copyGraphProperties[target,source,#]&];
];  

SetAttributes[copyGraphProperties,HoldFirst];

(* create a subgraph of g containing only the edges e 
   in contrast to Subgraph fullSubgraph also copies all Properties of edges and vertices in the subgraph *)
fullSubgraph[g_Graph,e:{(_UndirectedEdge|_DirectedEdge)..}] := Module[{gsub,esub},
	(* remove duplicate edges if there are any as Graph does not like duplicate edges in its inputs *)
	esub = DeleteDuplicates[e,edgeSameQ];	
	(* DO NOT USE Subgraph here! 
		Subgraph[g,e] can contain more edges than e ... *)
	gsub = Graph[esub];
	copyGraphProperties[gsub,g];
	Return[gsub];
]

(* create a Subgraph of g that contains only the path defined by the vertex list v *)
fullSubPathgraph[g_Graph,v_] := fullSubgraph[g,pathToEdges[v]]

xGridGraph[{n_,m_}] := Module[{g,xEdges},
	(* basic grid graph *)
	g = GridGraph[{n,m}];
	
	(* add X - edges in every rectangle in g *)
	(* / part *)
	xEdges = Drop[
		UndirectedEdge@@@Transpose@{Range[1,n*(m-1)-1],Range[n+2,n*m]}
		,
		{n,-1,n}
	];
	g = EdgeAdd[g,xEdges];
	(* \ part *)
	xEdges = Drop[
		UndirectedEdge@@@Transpose@{Range[2,n*(m-1)],Range[n+1,n*m-1]}
		,
		{n,-1,n}
	];
	g = EdgeAdd[g,xEdges];
		
	Return[g];
]

(* returns the vertice that is closest to x in the Graph g *)
closestVertice[g_Graph,x_] :=
	SortBy[
		vertexMap[g,{#,(complexCoordinates[g,#] - x) //Abs} &]
		,
		#[[2]] &
	] //First//First;

(* comparison of two edges
	in contrast to the Mathematica default we consider
	UndirectedEdge[a,b] == UndirectedEdge[b,a] 
	to be true and not false *)
edgeSameQ[e_DirectedEdge,f_DirectedEdge] := SameQ[e,f];
edgeSameQ[e_UndirectedEdge,f_UndirectedEdge] := SameQ[e,f] || SameQ[e,f//Reverse];

rescaleWeightsToDouble[g_Graph,opts:OptionsPattern[]] := Module[{vw,vwr,ew,ewr,gr,posv,pose,range},
	(* rescale VertexWeight and EdgeWeight so that its values can be represented with MachinePrecision numbers *)
	vw = PropertyValue[g,VertexWeight];
	ew = PropertyValue[g,EdgeWeight];
	(* only rescale non zero elements *)
	posv = selectPosition[vw,Positive];
	pose = selectPosition[ew,Positive];
	(* we rescale Log[*Weight] instead of *Weight as Rescale seems to have Problems with non MachinePrecision numbers *)
	vw[[posv]]  = vw[[posv]]  // Log;
	ew[[pose]]  = ew[[pose]]  // Log;
	(* determine range of weights *)
	range = {Min[#],Max[#]} &@ Join[ew[[pose]],vw[[posv]]];
	
	vwr = vw;
	ewr = ew;
	
	vwr[[posv]] = Rescale[vw[[posv]],range,OptionValue[rescaledRange]];
	vwr[[posv]] = vwr[[posv]] // Exp;
	
	ewr[[pose]] = Rescale[ew[[pose]],range,OptionValue[rescaledRange]];
	ewr[[pose]] = ewr[[pose]] // Exp;
	
	gr  = g;
	(* update Weights*)
	updateProperty[gr,VertexWeight,vwr];
	(* this function has been jused before we introduced the possibility to change the weight calculation
	ewr = edgeMap[gr, Mean @ vwr[[ List @@ # ]] &];
	*)
	updateProperty[gr,EdgeWeight,ewr];
	
	Return[gr];
]
Options[rescaleWeightsToDouble] = {rescaledRange->{-50,50}};

(* TODO: thrid value in result is ... well... random ... should be fixed if needed *)
MidpointRuleData[n_, pre_] := SetPrecision[{{1/2},{1},{Infinity}},pre];

linearPathNIntegrate[f_,zi_,opts:OptionsPattern[]] := Module[{x,w,werr,name,qf,post,z,zr,res,preFix,myMap},
	(* as there is no MidPointRule, we use the locally defined version *)
	If[OptionValue[Method] != "MidpointRule",
		name = "NIntegrate`" <> OptionValue[Method] <> "Data";
		,
		name = Context[linearPathNIntegrate] <> OptionValue[Method] <> "Data";
	];
	(* check if this name is actually an available quadrature forumula *)
	If[ ! NameQ[name],
		Abort[];	
	];
	myMap = If[useParallel//OptionValue,
		ParallelMap,
		Map
	];
	qf = ToExpression[name];
	{x,w,werr} = qf[ rulePoints//OptionValue, WorkingPrecision//OptionValue ];
	post = OptionValue[postProcessFunction];
	(* rescale x to linear path parts*)
	(* TODO remove this workaround if Wolfram fixes this bug *)
	(* Rescale sometimes throws errors if z is complex an has MachinePrecision *)
	preFix = OptionValue[WorkingPrecision] /. Optional[n_,1] MachinePrecision :> n $MachinePrecision;
	z = SetPrecision[zi,preFix];
	(* cache f evaluations  -- not sure if that's really worth it*)
	(* g[zz_] := g[zz] = f[zz]; *)
	(* midpoint rule needs a special treatment as it does not contain the endpoints *)
	If[OptionValue[Method] != "MidpointRule",
		zr = Rescale[x,{0,1},#] & /@ z;
		res = myMap[ w . post[ (#[[-1]] - #[[1]]) f /@ # ] &, zr ];
		,
		zr = {#[[1]],Rescale[x//First,{0,1},#],#[[2]]} & /@ z;
		res = myMap[ w[[1]] post[ (#[[-1]] - #[[1]]) f[ #[[2]] ] ] &, zr ];
	];
	Return[res];
];
Options[linearPathNIntegrate] = {Method->"ClenshawCurtisRule",
								 rulePoints->4,
								 WorkingPrecision->MachinePrecision,
								 postProcessFunction->Identity,
								 useParallel->True};

(* integrate f along each edge in the List e *)
edgeNIntegrate[g_Graph,f_,e:{edgePattern..},opts:OptionsPattern[]] :=
	edgeNIntegrate[g,f,List@@@e,opts];
	
edgeNIntegrate[g_Graph,f_,e_,opts:OptionsPattern[]] := Module[{z,ze},
	(* convert vertex numbers in e to coordinates *)
	z = complexCoordinates[g];
	ze = Map[z[[#]] &,e,{2}];
	ze = SetPrecision[ze,WorkingPrecision//OptionValue]; 
	Return[ linearPathNIntegrate[f,ze,FilterRules[{opts},Options[linearPathNIntegrate]]] ];
]
(* copy options from linearPathNIntegrate *)
Options[edgeNIntegrate] = Options[linearPathNIntegrate];

(* plot functions used by SEWContourPlot *)
pathPlot[g_Graph,v_?VectorQ] := Graphics[{Thickness[0.01],Blue,Line@listPropertyValue[g,VertexCoordinates,v]}];

trafficLight[range_] := 
  Module[{}, 
   Return[ColorDataFunction["trafficLight", "Gradients", range, 
      Function[Blend[List[Darker[Green], Yellow, Darker[Red]],
        Clip[
         Rescale[Slot[1], range],
         {0, 1}
         ]
        ]
       ]]];];

extractVertexProperty[g_Graph,p_,opts:OptionsPattern[]] := Module[{res,f},
	f = OptionValue[postProcess];
	res = ConstantArray[0,{g//VertexCount,3}];
	res[[All,{1,2}]] = PropertyValue[g,VertexCoordinates]; 
	res[[All,3]] = PropertyValue[g,p] //f;
	Return[res];
]
extractVertexProperty[g_Graph,p_,v_,opts:OptionsPattern[]] := With[{f = OptionValue[postProcess]},
		Append[ PropertyValue[{g,#},VertexCoordinates],
				PropertyValue[{g,#},p] //f
		]& /@ v
]
Options[extractVertexProperty] = {postProcess->Identity};

vertexPropertyContourPlot[g_Graph,p_,opts:OptionsPattern[]] :=
	ListContourPlot[
		extractVertexProperty[g,p,FilterRules[{opts},Options[extractVertexProperty]]]
		,
		FilterRules[{opts},Options[ListContourPlot]
	]
];
Options[vertexPropertyContourPlot] = Join[Options[extractVertexProperty],Options[ListContourPlot]];

vertexWeightContourPlot[g_Graph,opts:OptionsPattern[]] := 
	vertexPropertyContourPlot[g,VertexWeight, opts]
Options[vertexPropertyContourPlot] = Options[vertexPropertyContourPlot];

vertexWeightLogContourPlot[g_Graph,opts:OptionsPattern[]] := With[{cf = trafficLight[{-16,16}][#] &},
	vertexPropertyContourPlot[g,VertexWeight,postProcess->Log10,
											 ColorFunction->(cf[#] &),
											 ColorFunctionScaling -> False,
											 Contours -> {-16, -12, -8, -4, 0, 4, 8, 12, 16},
											 opts
	]
];
vertexWeightLogContourPlot[g_Graph,p_,opts:OptionsPattern[]] := With[{cf = trafficLight[{-16,16}][#] &,wm=Max@Log10@listPropertyValue[g,VertexWeight,p]},
	vertexPropertyContourPlot[g,VertexWeight,postProcess->Log10,
											 ColorFunction->(cf[#-wm] &),
											 ColorFunctionScaling -> False,
											 Contours -> wm+{-16, -12, -8, -4, 0, 4, 8, 12, 16},
											 PlotRange->All,
											 Axes->False,
											 Frame->False,
											 opts
	]
];
Options[vertexWeightLogContourPlot] = Options[vertexPropertyContourPlot];

End[]