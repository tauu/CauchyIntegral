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

(* This file contains some fixes / workaround for the Graph API of Mathematica 8 *)


vertexAdd::usage = "vertexAdd[g,v,vc,vw] adds the Vertexes v to g and sets\
 their VertexCoordiantes Property to vc and their VertexWeight Property to vw"
edgeAdd::usage = "edgeAdd[g,e,ew] adds the edges e to g and sets their\
 EdgeWeight Property to ew, unless ew is missing in which case it is set to 0."
edgeDelete::usage = ""
listPropertyValue::usage=""

Begin["`Private`"];
	(* DO NOT try to plot a Graph with more than 200 nodes,
	   just because it happens to be in the output. 
	   This takes forever and is more or less pointless anyway.
	   Especially if the Graph is just in the output because 
	   a function created an error, it takes unecessary long
	   to show the error message as the the graph has to be
	   formatted even though nobody is interested in it.
	   This has been fixed in Mathematica Version 10. :-) *)
If[ $VersionNumber < 10,
        Unprotect[Graph];
        Graph /:  Format[g_Graph?(VertexCount[#] >= 200 &),StandardForm] := 
                "Graph: |V|=" <> ToString@VertexCount@g <> ", |E|=" <> ToString@EdgeCount@g;
        Protect[Graph];
];

(* list of builtin graph properties *)
builtinProperties = {
		EdgeShapeFunction,
		EdgeStyle,
		EdgeWeight,
		GraphHighlight,
		GraphHighlightStyle,
		GraphLayout,
		GraphStyle,
		VertexCoordinates,
		VertexShape,
		VertexShapeFunction,
		VertexSize,
		VertexStyle,
		VertexWeight
};

(* edgeData[n,e] creates the datastructure that Graph uses to store edge information
 efficiently, with n being the number of vertexes in the Graph and e being the number of Edges *)
edgeData[n_,e_List] := {Null,SparseArray[ Join[ e , Reverse /@ e ] -> 1,{n,n}]};

(* propertyData[g] extracts the datastructure for all properties of a Graph,
 so that it can be used to create a new graph with the same properties *)
propertyData[g_] := Module[{pl,pout,pb,pc,pbl},
	pl = PropertyList@g;
	(* builtin Properties *)
	pbl = builtinProperties;
	(* pbl should contain all Properties that a Graph will always have *)
	pb = Cases[pl,
		Alternatives@@pbl
		];
	(* custom Properties *)
	pc = Cases[pl,
		Except[Alternatives@@pbl]
	];
	(* create stucture that the Graph function expects for the Properties *)
	pout = Append[
		 # -> PropertyValue[g,#] &/@ pb
		 ,
		 Properties -> 
		 	{"GraphProperties" -> ( # -> PropertyValue[g,#] &/@ pc)}
	];
	Return[pout];
]; 

(* Extend VertexAdd so that you can also set the VertexCoordinates Property for the 
   new nodes. This is neccessary as the VertexCoordinates Property of a graph cannot
   be changed after the grap has been created. Only the VertexCoordinates Property 
   of single Vertex can be changed, but this is very slow. 
   
   vertexAdd[g,v,vc,vw] adds the Vertexes v to g and sets their VertexCoordiantes 
   Property to vc and their VertexWeight Property to vw *)
vertexAdd[g_Graph,va_,vc_,vw_:Null] := Module[{gout,pout,v,e,vout},
	(* rebuild graph because we cannot set the VertexCoordiantes Property otherwise*)	
	v = VertexList@g;
	e = EdgeList@g;
	vout = Join[v,va];
	pout = propertyData[g];
	(* append new VertexCoordiantes *)
	pout = pout /. (VertexCoordinates -> l_) :> (VertexCoordinates -> Join[l,vc]);
	(* set VertexWeight of new Vertexes to 0, or vw if possible *)
	If[ (VertexWeight /. pout) =!= Automatic,
		pout = If[vw === Null,
			pout /. (VertexWeight -> l_) :> (VertexWeight -> PadRight[l,Length@vout])
			,
			pout /. (VertexWeight -> l_) :> (VertexWeight -> Join[l,vw])
		];
	];
	(* build new graph *)
	gout = Graph[vout,edgeData[Length@vout,List@@@e],Sequence@@pout];
	Return[gout];
];

(* extend EdgeAdd so that one can also direclty set the EdgeWeight Property of the
   new edge and keeps the EdgeWeight Property of the existing edges. EdgeAdd drops
   the EdgeWeight Property of all Edges. *)
edgeAdd[g_Graph,ea_,ew_:Null] := Module[{gout,ewn,ewa,i,io},
	gout = EdgeAdd[g,ea];
	ewa = If[ ew === Null,
		ConstantArray[0,Length@ea]
		,
		ew
	];
	(* add new EdgeWeights *)
	If[WeightedGraphQ[g],
		i = EdgeIndex[gout,#] &/@ ea;
		io = Ordering[i];
		ewn = PropertyValue[g,EdgeWeight];
		MapThread[
			( ewn = Insert[ewn,#1,#2]; )&,
			{ewa[[io]],i[[io]]}
		];
		updateProperty[gout, EdgeWeight, ewn];
	
	];
	Return[gout];
];

edgeDelete[g_Graph,ed_] := Module[{gout,ei},
	gout = EdgeDelete[g,ed];
	ei = EdgeIndex[g,#] &/@ ed;
	(* fix EdgeWeight *)
	(* TODO: Test if delete is fast in this case *)
	If[WeightedGraphQ[g],
		updateProperty[gout, EdgeWeight, Delete[PropertyValue[g,EdgeWeight],List/@ei]];
	];
	Return[gout];
];

(* test if a graph has a specific property *)
hasProperty[g_Graph,pName_] := MemberQ[PropertyList[g],pName];

(* set a property of a graph properly *)
setProperty[g_Graph,p_,val_] := Module[{v,e,pout,gout},
	v = VertexList@g;
	e = EdgeList@g;
	pout = propertyData[g];
	If[hasProperty[g,p],
		(* replace the current property value *)
		pout = pout /. (p -> _) -> (p -> val);	
		,
        (* builtin properties are set directly, all other properties are appended to GraphProperties *)
        If[ MemberQ[builtinProperties,p],
                pout = Insert[pout,p->val,-2]; 
		,
                pout = pout /. ("GraphProperties" -> {a : ___} ) -> ("GraphProperties" -> {a, p -> val});
        ];
	];
	(* build new graph *)
	gout = Graph[v,edgeData[Length@v,List@@@e],Sequence@@pout];
	Return[gout];
];

(* wrapper for PropertyValue / setProperty
   As setting properties works differently in Mathematica 8, 9 and 10
   (and maybe also in future versions...) this wrapper conveniantly handles updating properties
   by using the appropriate method.
    *)
updateProperty[g_,p_,val_] := Module[{},
	If[ $VersionNumber == 10,
		(* Mathematica 10 *)
		If[ MemberQ[builtinProperties,p] && PropertyValue[g,p] === Automatic,
			(* builtin properties can be set if they have not been initialized *)
			PropertyValue[g,p] = val;
			,
			(* in all other cases the property has to be set the hard way using setProperty *)
			g = setProperty[g,p,val];	
		];
		,
		(* Mathematica versions before 10 and hopefully also later versions *)
		PropertyValue[g,p] = val;
	];
];
SetAttributes[updateProperty,HoldFirst];

(* get the PropertyValue of the property p for a list of Graph parts *)
listPropertyValue[g_Graph,p_,v_List] := PropertyValue[{g,#},p] & /@ v 

(* fix value of vertexcoordinates - Mathematica Versions > 9 need special
   treatment if this property is set to automatic *)
fixVertexCoordinates[g_] := Module[{},
	(* WORKAROUND for Mathematica 9 / 9.0.1 - VertexCoordinates will be set to automatic if we do not assign one value by hand *)
	If[ $VersionNumber >= 9 && $VersionNumber < 10,
                PropertyValue[{g,1},VertexCoordinates] = PropertyValue[{g,1},VertexCoordinates];
	];
	(* WORKAROUND fot Mathematica 10 - VertexCoordinates will be set to automatic if we do not assign them by hand 
	   setting only one value does not work anymore *)
	If[ $VersionNumber >= 10,
                PropertyValue[g,VertexCoordinates] = listPropertyValue[g,VertexCoordinates,VertexList@g];
	];	
]
SetAttributes[fixVertexCoordinates,HoldFirst];

(* test if a graph has EdgeWeight and VertexWeight properties
   and if their values are numeric. The build-in function WeightedGraphQ 
   does not perform the last check, although this is necessary for functions
   like FindShortestPath *)
weightedGraphQ[g_Graph]  := Module[{},
	If[ ( GraphQ[g] && 
		WeightedGraphQ[g] && 
		MemberQ[PropertyList[g],EdgeWeight]	&&
		MemberQ[PropertyList[g],VertexWeight] &&
		VectorQ[PropertyValue[g,EdgeWeight]] &&
		VectorQ[PropertyValue[g,VertexWeight]] &&
		And@@NumericQ/@PropertyValue[g,EdgeWeight] &&
		And@@NumericQ/@PropertyValue[g,VertexWeight]
		)
		,
		True
		,
		False	
	]
]

weightedGraphDebug[g_Graph]  := Module[{},
	Print["GraphQ"];
	Print[GraphQ[g]]; 
	Print["WeightedGraphQ"];
	Print[WeightedGraphQ[g]];
	Print["has EdgeWeight"];
	Print[MemberQ[PropertyList[g],EdgeWeight]];
	Print["has VertexWeight"];
	Print[MemberQ[PropertyList[g],VertexWeight]];
	Print["EdgeWeight is vector"];
	Print[VectorQ[PropertyValue[g,EdgeWeight]]];
	Print["VertexWeight is vector"];
	Print[VectorQ[PropertyValue[g,VertexWeight]]];
	Print["EdgeWeight is numeric"];
	If[ And@@NumericQ/@PropertyValue[g,EdgeWeight]
		,
		Print[True];
		,
		Print[False];	
		Print["- Problematic Edges:"];
		Print[Pick[ {EdgeList@g,PropertyValue[g,EdgeWeight]}//Transpose, NumericQ/@PropertyValue[g,EdgeWeight], False ]];
	];
	Print["VertexWeight is numeric"];
	Print[And@@NumericQ/@PropertyValue[g,VertexWeight]];
];

machinePrecisionWeightedGraphQ[g_Graph] := With[{ew = PropertyValue[g,EdgeWeight],vw = PropertyValue[g,VertexWeight]},
	weightedGraphQ[g] 
	  && Max[ew] < $MaxMachineNumber && Min[ew] > $MinMachineNumber
	  && Max[vw] < $MaxMachineNumber && Min[vw] > $MinMachineNumber
];
Attributes[machinePrecisionWeightedGraphQ] = {Listable};

End[];