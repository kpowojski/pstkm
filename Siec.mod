#Sets
set CENTRAL;						#Wezel centralny (zbior jednoelementowy)
set TRANSPORT_NODE;					#Zbior wezlow transportowych
set DEMAND;  						#Zapotrzebowania
set CABLE_TYPE;                     #Zbior grubosci kabla

set NODES := CENTRAL union DEMAND union TRANSPORT_NODE;   #Wszystkie wezly w naszej topologii sieci
set L := (NODES cross NODES);      			#Polaczenia logiczne pomiedzy wezlami

set PATH within (NODES cross NODES);  			#Zbior sciezek - polaczen fizycznych miedzy wezlami

#Params	    
param hd {DEMAND} >= 0;         		#zapotrzebowanie aka liczba wlokien 
param M0 >= 0;		   			#zysk jednostkowy z realizacji 1 zapotrzebowania
param hc {CABLE_TYPE} >= 0;         		#koszt polozenia kabla danego typu
param TRENCHING_COST {PATH};					#trenching cost kabla
param CABINET_COST >= 0;             		#stala definujaca koszt umieszczenia cabinetu w wezle transportowym

#parametry originates/terminates dla modelu "logicznego"				  
param ae {n in NODES, (i,j) in L} binary :=	    		# ae - wykłady - konieczne do kirchhoffa
      if (i = n) then 1
    else 0; 
param be {n in NODES, (i,j) in L} binary :=				# be - wyklady - konieczne do kirchhoffa
      if (j = n) then 1
    else 0; 

#parametry originates/terminates dla modelu "fizycznego"			 
param ape {n in NODES, (i,j) in PATH} binary :=	    	# ae - wykłady - konieczne do kirchhoffa
      if (i = n) then 1
    else 0; 
param bpe {n in NODES, (i,j) in PATH} binary :=			# be - wyklady - konieczne do kirchhoffa
      if (j = n) then 1
    else 0; 

param sum_d := sum{l in DEMAND} hd[l]; 					# suma wszystkich zapotrzebowan

param path_counter = card(PATH);						# suma wszystkich krawedzi w modelu fizycznym
	
var Xed {(i, j) in L, k in CENTRAL, l in DEMAND, m in CABLE_TYPE} binary;				#zapotrzebowania na polaczeniu w modelu logicznym 
var XXed {(i, j) in PATH, (k,l) in L, m in CABLE_TYPE} binary;						#zapotrzebowania na polaczeniu w modelu fizycznym
var d_served {k in CENTRAL, l in DEMAND} binary;    							#realizowane zapotrzebowania - zmienna binarna
var hpd {L};
var cables{PATH, CABLE_TYPE} binary;
var is_cable_used{(i,j) in PATH} binary;
var is_cabinet{NODES} binary;




maximize Profit:       	  							#f. celu
	 sum{k in CENTRAL ,l in DEMAND}(d_served[k,l] * M0 * hd[l])
	-sum{(i,j) in PATH, m in CABLE_TYPE}(cables[i,j,m]*hc[m])
    -(sum{n in NODES}is_cabinet[n])*CABINET_COST
	-sum{(i,j) in PATH}is_cable_used[i,j]*TRENCHING_COST[i,j]
;

# suma zapotrzebowan na krawedzi musi byc wieksza niz suma logicznych polaczen
subject to demand{(i,j)in L}:
        hpd[i,j] >= sum{k in CENTRAL, l in DEMAND, m in CABLE_TYPE} Xed[i,j,k,l,m]*hd[l]; 
		

# suma zapotrzebowan na konkretnej krawedzi jest mniejsza rowna sumie wszystkich zapotrzebowan		
subject to usage_l{(i,j) in L, m in CABLE_TYPE}:
	(sum {k in CENTRAL,l in DEMAND} Xed[i,j,k,l,m]*m) <= sum_d;

# zmienna pomocnicza
subject to demand_on_edge{(i,j) in PATH, m in CABLE_TYPE}:
    (cables[i,j,m]) >= (sum{(k,l) in L}XXed[i,j,k,l,m]);

# sprawdzenie czy kabel jest wykorzystywany
subject to path_exists{(i,j) in PATH, m in CABLE_TYPE}:
	cables[i,j,m]*m <= is_cable_used[i,j]*sum_d;
	
# sprawdzanie wstawić cabinet w danym wezle transportowym
subject to cabinet_needed{n in TRANSPORT_NODE}:
		sum{(i,j) in PATH, m in CABLE_TYPE} (ape[n,i,j]-bpe[n,i,j])*cables[i,j,m] <= path_counter*is_cabinet[n];


# wymog zeby byl jeden kabel na krawedzi
subject to one_cable_on_path{(i,j) in PATH}:
		sum{m in CABLE_TYPE} cables[i,j,m] <= 1;
	
# kirchhoff dla sciezek logicznych
subject to Kirchhoff{n in NODES, k in CENTRAL, l in DEMAND}:
	(sum {(i, j) in L, m in CABLE_TYPE} ae[n,i,j]*Xed[i,j,k,l,m]*m)
	- (sum {(i,j) in L, m in CABLE_TYPE} be[n,i,j]*Xed[i,j,k,l,m]*m) =
	(if n = k then hd[l]*d_served[k,l] else if n = l then - hd[l]*d_served[k,l] else 0);

# kirchhoff dla sciezek 
subject to Kirchhoff_Paths{n in NODES, (k,l) in L}:
	(sum {(i, j) in PATH, m in CABLE_TYPE} ape[n,i,j]*XXed[i,j,k,l,m]*m)
	- (sum {(i,j) in PATH, m in CABLE_TYPE} bpe[n,i,j]*XXed[i,j,k,l,m]*m) =
        (if n = k then hpd[k,l] else if n = l then - hpd[k,l] else 0);
