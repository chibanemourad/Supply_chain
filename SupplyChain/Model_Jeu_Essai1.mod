/*********************************************
 * OPL 12.5 Model
 * Author: CHIMOU
 * Creation Date: 27 oct. 2012 at 15:50:23
 *********************************************/
 /*Structure de données Arc_Entre represente un lien entre deux entité exp : Usine---->Fournisseur*/
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
int Qu_Prod=...;
range SousTraitant=1..N_SsTraitant;
range Entrepot=1..N_Entrepot;
range Usine=1..N_Usine;

/*Liaisons : */
/*Entre Usine et Sous-Traitant*/
{Arc_Entre} U_S=...;
/*Entre Usine et Fournisseur*/
{Arc_Entre} U_F=...;
/*Entre Usine et Entrepot*/
{Arc_Entre} U_E=...;

/*Declaration des var pour les couts*/
int CoutUS[U_S]=...;//Cout entre Usine et Sous-Traitant
int CoutUF[U_F]=...;//Cout entre Usine et Fournisseur
int CoutUE[U_E]=...;//Cout entre Usine et Entrepot
int CoutUsine[Usine]=...; //Cout Production U1=4€ U2=6€ U3=6€
int Cout_Fix_Usine[Usine]=...;//Cout fix pour les usines 1000
int Cout_Fix_SsTrait[SousTraitant]=...;//Cout fix pour les usines 500
int Cout_Fix_Entrepot[Entrepot]=...;//Cout fix pour les usines 200

/*Variables de decisions*/
/* Choix ou non d'utiliser[entite]=1 si OUI & 0 SINON */
dvar int+ Usine_Choisi[Usine];
dvar int+ Entrepot_Choisi[U_E];
dvar int+ SsTrait_Choisi[U_S];
/* Decider de la quantité à produire a acheter ou a stocker [entite]*/
dvar int+ Produire_Qu[Usine];
dvar int+ Achete_Qu_SsT[U_S];
dvar int+ Achete_Qu_F[U_F];
dvar int+ Stocker_Qu[U_E]; 

dexpr int Cout_Production= sum(i in Usine)((Produire_Qu[i]*CoutUsine[i]+Usine_Choisi[i]*Cout_Fix_Usine[i])+(sum(<x,k> in U_F:x==i)CoutUF[<i,k>]*Achete_Qu_F[<i,k>])+(sum(<c,l> in U_E:c==i)(CoutUE[<i,l>]*Stocker_Qu[<i,l>]+Entrepot_Choisi[<i,l>]*Cout_Fix_Entrepot[l]))+sum(<v,k> in U_S:v==i)((CoutUS[<i,k>]*Achete_Qu_SsT[<i,k>])+SsTrait_Choisi[<i,k>]*Cout_Fix_SsTrait[k]));
minimize Cout_Production;
 subject to{
 
    ct_Capacite_Prod_Usine:forall(i in Usine)Produire_Qu[i]<=800;
    ct_Plafond_Achat_SsTra:forall(<i,j> in U_S)(Achete_Qu_SsT[<i,j>]<=2000);
    ct_Capa_Stock_Entrepot:forall(<i,j> in U_E)Stocker_Qu[<i,j>]<=500;
    ct_Quantite_A_Produire:(sum(i in Usine)Produire_Qu[i])==Qu_Prod;
    ct_Capacite_Prod_SsTra:(sum(<i,j> in U_S)Achete_Qu_SsT[<i,j>])==2*Qu_Prod;
    ct_Choix_de_Usine: forall(i in Usine){Usine_Choisi[i]==0 && Produire_Qu[i]==0||Usine_Choisi[i]==1&&Produire_Qu[i]!=0;};
    ct_Choix_Sous_Traitant: forall(<i,j> in U_S){SsTrait_Choisi[<i,j>]==0 && Achete_Qu_SsT[<i,j>]==0||SsTrait_Choisi[<i,j>]==1&&Achete_Qu_SsT[<i,j>]!=0;};
    ct_Choix_Entrepot: forall(<i,j> in U_E){Entrepot_Choisi[<i,j>]==0 && Stocker_Qu[<i,j>]==0||Entrepot_Choisi[<i,j>]==1&&Stocker_Qu[<i,j>]!=0;};
    ct_QuPro_A_Stocker:(sum(<i,j> in U_E)Stocker_Qu[<i,j>])==Qu_Prod;
    ct_QuPro_Ach_ChezFour:(sum(<i,j> in U_F)Achete_Qu_F[<i,j>])==Qu_Prod;
    ct1:forall(i in Usine)(Produire_Qu[i]-(sum(<i,j> in U_F)Achete_Qu_F[<i,j>]))==0;
    ct2:forall(i in Usine)2*Produire_Qu[i]-(sum(<i,j> in U_S)Achete_Qu_SsT[<i,j>])==0;
    ct3:forall(i in Usine)(Produire_Qu[i]-(sum(<i,j> in U_E)Stocker_Qu[<i,j>]))==0;	
   };
   
  execute
 {	 
 	 writeln("");
 	 writeln("**********************************************************************************************");
     writeln("*                            Récapitulatif  des Usine choisies                               *");
     writeln("**********************************************************************************************");
       for(var a in Usine)
       {
        if(Produire_Qu[a]!=0)
        writeln("L'entreprise choisi de produire : ["+Produire_Qu[a]+"] Unité de Produit fini, dans l'Entreprise N° : [" +a+"]");
     } 
 	 writeln("");
   	 writeln("**********************************************************************************************");
     writeln("*                              01- Choix des Sous Traitants                                  *");
     writeln("**********************************************************************************************");
     for(var a in U_S)
      {
        if(Achete_Qu_SsT[a]!=0)
         writeln("Usine N° : ["+a.node1+"] Achete : ["+Achete_Qu_SsT[a]+"] Pièces, chez le Sous-Traitant N° : [" + a.node2 +"]");
    	}
	 writeln("");    	     
     writeln("**********************************************************************************************");
     writeln("*                                 02- Choix des Fournisseurs                                 *");
     writeln("**********************************************************************************************");
       for(var a in U_F)
       {
        if(Achete_Qu_F[a]!=0)
        writeln("Usine N° : ["+a.node1+"] Achete : ["+Achete_Qu_F[a]+"] Unité de matière première, chez le Sous-Traitant N° : [" +a.node2+"]");
     }       
     writeln("");    	     
     writeln("**********************************************************************************************");
     writeln("*                                    03- Choix des Entrepots                                 *");
     writeln("**********************************************************************************************");
       for(var a in U_E)
       {
        if(Stocker_Qu[a]!=0)
        writeln("Usine N° : ["+a.node1+"] Stocke : ["+Stocker_Qu[a]+"] Unité de Produit fini, dans l'Entrepot N° : [" +a.node2+"]");
     }       

       writeln("");
       writeln("");      
       writeln("*********************************************************************************************");
       writeln("Coût minimal pour la production de ["+Qu_Prod+"] Unité de produit fini = : "+Cout_Production+" €");
  }