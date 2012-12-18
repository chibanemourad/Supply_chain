/*********************************************
 * OPL 12.5 Model
 * Author: CHIMOU
 * Creation Date: 12 déc. 2012 at 02:06:29
 *********************************************/
tuple Arc_Entre
{
  int node1;
  int node2;
};

/*Constantes : */
int N_Usine=...;
int N_SsTraitant=...;
int N_Entrepot=...;
int N_Fournisseur=...;
int N_Produits=...;
range SousTraitant=1..N_SsTraitant;
range Entrepot=1..N_Entrepot;
range Usine=1..N_Usine;
range Produit=1..N_Produits;
int Qu_Prod[Produit]=...;
int Qu_P_Fourni[Produit]=...;
int Qu_P_SsTrai[Produit]=...;

/*Liaisons : */
/*Entre Usine et Sous-Traitant*/
{Arc_Entre} U_S=...;
/*Entre Usine et Fournisseur*/
{Arc_Entre} U_F=...;
/*Entre Usine et Entrepot*/
{Arc_Entre} U_E=...;

/*Declaration des var pour les couts*/
int CoutUS[Produit][U_S]=...;//Cout entre Usine et Sous-Traitant
int CoutUF[Produit][U_F]=...;//Cout entre Usine et Fournisseur
int CoutUE[Produit][U_E]=...;//Cout entre Usine et Entrepot
int CoutUsine[Produit][Usine]=...; //Cout Production U1=4€ U2=6€ U3=6€
int Cout_Fix_Usine[Produit][Usine]=...;//Cout fix pour les usines 1000
int Cout_Fix_SsTrait[Produit][SousTraitant]=...;//Cout fix pour les usines 500
int Cout_Fix_Entrepot[Produit][Entrepot]=...;//Cout fix pour les usines 200

/*Variables de decisions*/
/* Choix ou non d'utiliser[entite]=1 si OUI & 0 SINON */
dvar int+ Usine_Choisi[Produit][Usine];
dvar int+ Entrepot_Choisi[Produit][U_E];
dvar int+ SsTrait_Choisi[Produit][U_S];
/* Decider de la quantité à produire a acheter ou a stocker [entite]*/
dvar int+ Produire_Qu[Produit][Usine];
dvar int+ Achete_Qu_SsT[Produit][U_S];
dvar int+ Achete_Qu_F[Produit][U_F];
dvar int+ Stocker_Qu[Produit][U_E]; 

dexpr int Cout_Production= sum(s in Produit)sum(i in Usine)((Produire_Qu[s][i]*CoutUsine[s][i]+Usine_Choisi[s][i]*Cout_Fix_Usine[s][i])+(sum(<x,k> in U_F:x==i)CoutUF[s][<i,k>]*Achete_Qu_F[s][<i,k>])+(sum(<c,l> in U_E:c==i)(CoutUE[s][<i,l>]*Stocker_Qu[s][<i,l>]+Entrepot_Choisi[s][<i,l>]*Cout_Fix_Entrepot[s][l]))+sum(<v,k> in U_S:v==i)((CoutUS[s][<i,k>]*Achete_Qu_SsT[s][<i,k>])+SsTrait_Choisi[s][<i,k>]*Cout_Fix_SsTrait[s][k]));
minimize Cout_Production;
 subject to{
 
    ct_Capacite_Prod_Usine:forall(i in Usine)sum(s in Produit)Produire_Qu[s][i]<=800;
    ct_Plafond_Achat_SsTra:forall(j in SousTraitant)(sum(<i,j> in U_S)(sum(s in Produit)(Achete_Qu_SsT[s][<i,j>]))<=3000);
    ct_Capa_Stock_Entrepot:forall(<i,j> in U_E)sum(s in Produit)Stocker_Qu[s][<i,j>]<=500;
    ct_Quantite_A_Produire:forall(s in Produit){(sum(i in Usine)Produire_Qu[s][i])==Qu_Prod[s];};
    ct_Capacite_Prod_SsTra:forall(s in Produit)(sum(<i,j> in U_S)Achete_Qu_SsT[s][<i,j>])==Qu_P_SsTrai[s]*Qu_Prod[s];
    ct_Choix_de_Usine:forall(s in Produit)forall(i in Usine){Usine_Choisi[s][i]==0 && Produire_Qu[s][i]==0||Usine_Choisi[s][i]==1&&Produire_Qu[s][i]!=0;};
    ct_Choix_Sous_Traitant: forall(s in Produit)forall(<i,j> in U_S){SsTrait_Choisi[s][<i,j>]==0 && Achete_Qu_SsT[s][<i,j>]==0||SsTrait_Choisi[s][<i,j>]==1&&Achete_Qu_SsT[s][<i,j>]!=0;};
    ct_Choix_Entrepot: forall(s in Produit)forall(<i,j> in U_E){Entrepot_Choisi[s][<i,j>]==0 && Stocker_Qu[s][<i,j>]==0||Entrepot_Choisi[s][<i,j>]==1&&Stocker_Qu[s][<i,j>]!=0;};
    ct_QuPro_A_Stocker:forall(s in Produit)(sum(<i,j> in U_E)Stocker_Qu[s][<i,j>])==Qu_Prod[s];
    ct_QuPro_Ach_ChezFour:forall(s in Produit)(sum(<i,j> in U_F)Achete_Qu_F[s][<i,j>])==Qu_Prod[s]*Qu_P_Fourni[s];
    
    ct1:forall(s in Produit)forall(i in Usine)(Qu_P_Fourni[s]*Produire_Qu[s][i]-(sum(<i,j> in U_F)Achete_Qu_F[s][<i,j>]))==0;
    ct2:forall(s in Produit)forall(i in Usine)Qu_P_SsTrai[s]*Produire_Qu[s][i]-(sum(<i,j> in U_S)Achete_Qu_SsT[s][<i,j>])==0;
    ct3:forall(s in Produit)forall(i in Usine)(Produire_Qu[s][i]-(sum(<i,j> in U_E)Stocker_Qu[s][<i,j>]))==0;
    
   };
     	  
  execute DISPLAY
 {	 
 
 	  writeln("**********************************************************************************************");
      writeln("*                            Récapitulatif  des Usine choisies                               *");
      writeln("**********************************************************************************************");
       for(var s in Produit)
       {writeln("Produit de type :",s)
       for(var a in Usine)
       {
         if(Produire_Qu[s][a]!=0)
         writeln("L'entreprise choisi de produire : ["+Produire_Qu[s][a]+"] Unité de Produit fini de type ["+s+"], dans l'Entreprise N° : [" +a+"]");
       }    }
      
	 writeln("");
 	 writeln("**********************************************************************************************");
     writeln("*                                 CHOIX DES SOUS TRAITANTS                                    *");
     writeln("**********************************************************************************************");
     for(var s in Produit)
     {writeln("produit de type :",s)
     for(var a in U_S)
      {
         if(Achete_Qu_SsT[s][a]!=0)
         writeln("Usine N° : ["+a.node1+"] Achete : ["+Achete_Qu_SsT[s][a]+"] Pièces, pour le produit ["+s+"], chez le Sous-Traitant N° : [" + a.node2 +"]");
      }    }
   
   	   
   	 writeln("**********************************************************************************************");
     writeln("*                                 CHOIX DES FOURNISSEURS                                     *");
     writeln("**********************************************************************************************");
       for(var s in Produit)
       {writeln("Produit de type :",s)
       for(var a in U_F)
       {
        if(Qu_P_Fourni[s][a]!=0)
       writeln("Usine N° : ["+a.node1+"] Achete : ["+Achete_Qu_F[s][a]+"] Unité de matière première, pour le produit ["+s+"], chez le Fournisseur N° : [" +a.node2+"]");
     }  }  
     
     writeln("**********************************************************************************************");
     writeln("*                                 CHOIX DES ENTREPOTS                                        *");
     writeln("**********************************************************************************************"); 
       for(var s in Produit)
       {writeln("Produit de type :",s)
       for(var a in U_E)
       {
        if(Stocker_Qu[s][a]!=0)
        writeln("Usine N° : ["+a.node1+"] Stocke : ["+Stocker_Qu[s][a]+"] Unité de Produit fini de type ["+s+"], dans l'Entrepot N° : [" +a.node2+"]");
     }   }    
     
     writeln("");
       writeln("");      
       writeln("*********************************************************************************************");
       writeln("Coût minimal pour la production de ["+Qu_Prod+"] Unité de produit fini = : "+Cout_Production+" €");  

  }