#Sets
set CENTRAL;						#Wezel centralny (zbior jednoelementowy)
set T;								#Zbior wezlow transportowych
set D;  							#Zapotrzebowania
set N := CENTRAL union D union T;   #Wszystkie wezly w naszej topologii sieci
set L := (N cross N);      			#Polaczenia logiczne pomiedzy wezlami
set C;                     			#Zbior grubosci kabla
set P within (N cross N);  			#Zbior sciezek - polaczen fizycznych miedzy wezlami

#Params	    
param hd {D} >= 0;         		#zapotrzebowanie aka liczba wlokien 
param M >= 0;		   			#zysk jednostkowy z realizacji 1 zapotrzebowania
param hc {C} >= 0;         		#koszt polozenia kabla danego typu
param TC {P};					#trenching cost kabla
param NU >= 0;             		#stala definujaca koszt umieszczenia cabinetu w wezle transportowym

#parametry originates/terminates dla modelu "logicznego"				  
param ae {n in N, (i,j) in L} binary :=	    		# ae - wykłady - konieczne do kirchhoffa
      if (i = n) then 1
    else 0; 
param be {n in N, (i,j) in L} binary :=				# be - wyklady - konieczne do kirchhoffa
      if (j = n) then 1
    else 0; 

#parametry originates/terminates dla modelu "fizycznego"			 
param ape {n in N, (i,j) in P} binary :=	    	# ae - wykłady - konieczne do kirchhoffa
      if (i = n) then 1
    else 0; 
param bpe {n in N, (i,j) in P} binary :=			# be - wyklady - konieczne do kirchhoffa
      if (j = n) then 1
    else 0; 

param sum_d := sum{l in D} hd[l]; 					# suma wszystkich zapotrzebowan

param path_counter = card(P);						# suma wszystkich krawedzi w modelu fizycznym
	
var Xed {(i, j) in L, k in CENTRAL, l in D, m in C} binary;				#zapotrzebowania na polaczeniu w modelu logicznym 
var XXed {(i, j) in P, (k,l) in L, m in C} binary;						#zapotrzebowania na polaczeniu w modelu fizycznym
var d_served {k in CENTRAL, l in D} binary;    							#realizowane zapotrzebowania - zmienna binarna
var hpd {L};
var cables{P, C} binary;
var is_cable_used{(i,j) in P} binary;
var is_cabinet{N} binary;




maximize Profit:       	  							#f. celu
	 sum{k in CENTRAL ,l in D}(d_served[k,l] * M * hd[l])
	-sum{(i,j) in P, m in C}(cables[i,j,m]*hc[m])
    -(sum{n in N}is_cabinet[n])*NU
	-sum{(i,j) in P}is_cable_used[i,j]*TC[i,j]
;

subject to demand{(i,j)in L}:
        hpd[i,j] >= sum{k in CENTRAL, l in D, m in C}Xed[i,j,k,l,m]*m;
		# hpd[i,j] = sum{k in CENTRAL, l in D, m in C}Xed[i,j,k,l,m]*m; #TAK_BYLO
		
subject to usage_l{(i,j) in L, m in C}:
	(sum {k in CENTRAL,l in D} Xed[i,j,k,l,m]*m) <= sum_d;


subject to demand_on_edge{(i,j) in P, m in C}:
        (cables[i,j,m]*m) >= (sum{(k,l) in L}XXed[i,j,k,l,m]*m);


subject to path_exists{(i,j) in P, m in C}:
	cables[i,j,m] <= is_cable_used[i,j]*sum_d;

subject to cabinet_needed{n in T}:
		sum{(i,j) in P, m in C} (ape[n,i,j]+bpe[n,i,j])*cables[i,j,m] <= path_counter*is_cabinet[n];
#        sum{(i,j) in P, m in C} (ape[n,i,j]+bpe[n,i,j])*cables[i,j,m]*m <= path_counter*is_cabinet[n]; TAK_BYLO
		
subject to Kirchhoff{n in N, k in CENTRAL, l in D}:
	(sum {(i, j) in L, m in C} ae[n,i,j]*Xed[i,j,k,l,m]*m)
	- (sum {(i,j) in L, m in C} be[n,i,j]*Xed[i,j,k,l,m]*m) =
	(if n = k then hd[l]*d_served[k,l] else if n = l then - hd[l]*d_served[k,l] else 0);

subject to Kirchhoff_Paths{n in N, (k,l) in L}:
	(sum {(i, j) in P, m in C} ape[n,i,j]*XXed[i,j,k,l,m]*m)
	- (sum {(i,j) in P, m in C} bpe[n,i,j]*XXed[i,j,k,l,m]*m) =
        (if n = k then hpd[k,l] else if n = l then - hpd[k,l] else 0);
