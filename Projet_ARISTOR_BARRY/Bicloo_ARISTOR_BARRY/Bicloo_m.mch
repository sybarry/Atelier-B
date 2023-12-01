/* Bicloo
 * Author: ARISTOR Christella, BARRY Saikou yaya
 * Creation date: 10/11/2023
 */
MACHINE 
    Bicloo_m

SETS
    Bicloos;   //ensembles abstraits
    Parc;      //ensembles abstraits
    Place      //ensembles abstraits
    
CONSTANTS
    maxBicloos,  //borne supérieur
    maxPlaces    //borne supérieur
    
PROPERTIES
    maxBicloos : 1..MAXINT
    & maxPlaces : 1..MAXINT  
    
VARIABLES
    bicloos,
    parcs,
    sousPlaces,
    biclooDansParc,  //variable d état
    sortiDeParc,       //variable d état pour mémoriser le bicloo sorti
    parcAvecPlace
    
INVARIANT
    bicloos <: Bicloos //sous ensemble des Bicloos utilisées
    & parcs <: Parc // sous ensemble des parcs utilisés
    & sousPlaces <: Place
    & biclooDansParc : Bicloos >+> sousPlaces // relation Bicloos -> Parc
    & parcAvecPlace : Parc --> sousPlaces
    & sortiDeParc : Bicloos --> BOOL //relation Bicloos -> BOOL pour savoir s'il est sorti
    
INITIALISATION
    bicloos := {}
    || sousPlaces := {}
    || parcs := {}
    || biclooDansParc := {}
    || sortiDeParc := {}
    || parcAvecPlace := {}
    
OPERATIONS
    sortirBicloo(bicloo, place) =
    PRE
        bicloo : Bicloos
        & place : Place
        & biclooDansParc(bicloo) = place
        & sortiDeParc(bicloo) = FALSE
    THEN
        sortiDeParc := sortiDeParc <+ {bicloo |-> TRUE}
    END
    ;
    
    rangerBicloo(bicloo, place) = 
    PRE
        bicloo : Bicloos
        & place : Place
        & bicloo /: bicloos
        & place /: Place
        & card(biclooDansParc) < maxBicloos
    THEN
        bicloos := bicloos \/ {bicloo}
        || sousPlaces := Place \/ {place}
        || biclooDansParc(bicloo) := place
        || sortiDeParc := sortiDeParc <+ {bicloo |-> FALSE}
    END
    ;
    
    ajouterParc(nouveauParc) =
    PRE
        nouveauParc : Parc
        & nouveauParc /: parcs
    THEN
        parcs := parcs \/ {nouveauParc}
    END
    ;
    
    supprimerParc(parcAsupprimer) =
    PRE
        parcAsupprimer : Parc
        & parcAsupprimer : parcs
    THEN
        parcs := parcs - {parcAsupprimer}
    END    
    ; 
    
    deplacerBicloo(bicloo, nvPlace) =
    PRE
        bicloo : Bicloos
        & nvPlace : Place
        & biclooDansParc(bicloo) /: Place
    THEN
        sousPlaces := (sousPlaces \/ {nvPlace}) - {place |  place : sousPlaces & place = biclooDansParc(bicloo)}
        || biclooDansParc(bicloo) := nvPlace
    END
    
END