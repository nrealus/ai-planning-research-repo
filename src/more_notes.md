**Motivation / objectif global**:

Un acteur capable:
- de résoudre des problèmes avec des caractéristiques numériques, temporelles, incertaines (temporellement et non-temporellement);
- de conduire leur résolution en temps réel en prenant dynamiquement des décisions:
  - garantissant (statistiquement) la validité de certains sous-ensembles de contraintes;
  - optimisant (statistiquement) des critères numériques (coût / utilité);
- prendre en compte des changements (observations, évolutions / mise à jour des objectifs / conditions / actions planifiées / belief (probabiliste) actuel) et s'y adapter par une "approche progressive" [1], çad un intercalage / combinaison:
  - d'une approche proactive [1]: prévision des possibilités / cas différents (plans conditionnels / contingents, lookahead);
  - d'une approche de révision (ou réactive) [1] - replanification / réparation de plans ou beliefs actuels.

[1] J.Bidot

**Architecture générale proposée**:



**Chronique étendue**:

Extension de la définition de chronique permettant d'exprimer des spécifications:
- d'incertitude;
- de "contraintes molles" (ou "de chance");
- d'optimisation (statistiquement - i.e. l'éspérance) de critère numérique.

`Chr = (V, I, tau, X, C, E, S, R, U)`. On notera `p_Chr` la variable / le littéral de présence de la chronique `Chr`.

`V, tau, X, C, E, S` - sens usuel.

`I` - spécification de probabilités conditionnelles (table / réseau bayésien / diagramme d'influence).

`U` - fonction (pseudo-booléenne?) décrivant un critère à optimiser (coût ou, alternativement, utilité). Pseudo-booléenne: termes "filtrés" par un littéral (ou une clause?). Si ce littéral ne tient pas, le terme est pris comme égal à 0. Similairement, `U = 0` quand `!p_Chr`.

`R` - "chroniques / contraintes molles / de chance". `R` est un ensemble de paires `(CChr_i, delta_i)`, où `CChr_i` est une (instance de?) chronique et `delta_i € ]0,1[`. Grossièrement, `delta_i` exprime le la "limite de risque" ou le "risque maximal toléré" d'invalidité de contraintes impliquées par la présence de `CChr_i` lorsque `Chr` est présente.

- Plusieurs possibilités à l'étude pour définir plus exactement la signification / sémantique des "chroniques / contraintes molles". Mais l'idée globale est de faire intervenir `p_CChr_i`, une espérance (`EE`), et enfin `delta_i`. Une formulation possible (!!juste une suggestion!!) pourrait être: `EE(!(p_Chr => p_CChr_i)) < delta_i`. Une autre possibilité (non-exclusive) et de faire figurer dans le coût `U` un terme (constant, par exemple `1`) "filtré" par une clause `!p_CChr_1 \/ ... \/ !p_CChr_k`. Il faudra aussi jouer avec des spécifications "structurelles", comme par exemple le fait que `p_CChr_i => p_Chr`.
  - Rappel 1: `EE(conjonction de variables aléatoires booléennes) = PP(toutes ces variables sont vraies (i.e. == 1))` (où `PP` dénote la probabilité).

**Définition et sémantique du problème de planification; stratégies / politiques d'exécution**:

Il est important de bien définir le sens des idées liées à l'incertitude et aux chroniques molles, car on pourrait rapidement se faire piéger par notre intuition, en premier lieu à cause des interprétations différentes qu'il pourrait y avoir à cause de la notion de temps...

Le problème qu'on veut résoudre est de construire incrémentellement (pas à pas) un plan conditionnel / contingent, correspondant à un arbre (alternativement, un MDD) représentant des options d'instantiation des variables des chroniques, dans un ordre temporel (par défaut, un ordre de "pire cas" où, en cas d'ambiguité, les variables contrôlables ont priorité sur les incontrôlables). Les chemins (jusqu'aux feuilles) de cet arbre correspondent à des chroniques / scénarios / traces (non-temporelles) complets, finaux.

Les options d'instantiation qu'on veut représenter / garder dans l'arbre sont celles dont qui permettent que:
- toute "contrainte dure" est satisfaite dans chaque scénario;
- toute "contrainte molle" n'est violée que dans une "proportion" (pourcentage / probabilité) de scénarios (scénarios corrects, avec satisfaction de toutes les "contraintes dures") inférieure à la "limite de risque" de la contrainte molle.

Le plan conditionnel / contingent que représentera cet arbre se "prend en charge" par une stratégie / politique d'exécution, que l'acteur suit pour concrètement "mettre en oeuvre" / exécuter la résolution du problème qui lui a été confié.

Les stratégies / politiques d'exécution que nous souhaitons que notre acteur suive doivent:
- suivre le principe d'utilité (i.e. choix des décisions (et leur temps / instant / moment) correspondant à la "maximum expected utility"). Autrement dit, la stratégie d'exécution devra choisir parmi les décisions "proposées" (ou "mises à disposition") dans le plan conditionnel, celles les plus susceptibles de mener à une trace / histoire d'exécution finale avec un critère (coût / utilité) optimal (minimal / maximal);
- être dynamiques.

Les stratégies / politiques d'exécution peuvent être statiques ou dynamiques. Dans le cas dynamique, les décisions sont prises "en temps réel", au fur et à mesure, en tenant compte des observations / de la trace d'exécution passée. Dans le cas statique, les décisions sont prises en amont, tout au début. Les stratégies / politiques statiques sont un cas particulier / sous-ensemble des stratégies / politiques dynamiques. On peut voir une politique statique comme une politique dynamique "qui s'entête" à faire des choix avec lesquels on l'a paramétrée en amont.

Ainsi, notre problème n'est pas seulement de construire un plan conditionnel / contingent, mais de construire un plan conditionnel / contingent qui puisse être mis en oeuvre par une stratégie / politique d'exécution dynamique (et suivant le principe d'utilité). Notre intérêt est de s'assurer que l'exécution dynamique (comme un PSTN/STNU) d'un scénario correspondant à un certain choix ne soit pas contradictoire avec la partie commune (passé) d'un scénario correspondant à un autre choix.

Pour s'assurer que le plan conditionnel / contingent qu'on construit est dynamique (i.e. qu'il peut être mis en oeuvre par une stratégie / politique d'exécution dynamique) - ou alternativement, qu'il n'est pas non-dynamique -, il faudra considérer des contraintes supplémentaires au cours de sa construction.

Peut-être qu'il faudra s'inspirer du vieux papier de Tsamardinos (2003)... mais avec des "insights" sur les cycles négatifs semi-reducibles, le processus d'aggrégation-combinaison des enveloppes dynamiques de Cui, et le DC-checking avec relaxations incrémentelles de Bhargava...?




Peut-être que nous devrions considérer les variables contrôlables de la même manière que les incontrôlables (au regard de la contrôlabilité dynamique) ?

En effet, dans le travail de Cui, c'est l'union des enveloppes DC qui est prise. Cela lui permet de trouver des conditions à observer sur les (une) durée incontrôlable précédant chaque choix d'alternative, sous lesquelles au moins une alternative pourrait mener à un scénario complet de manière dynamiquement contrôlable. Pour des choix /alternatives incontrôlables, il suffirait de prendre l'intersection, plutôt que l'union. Cela simplifierait d'ailleurs les choses - en effet, la complexité vient des "étages" successifs de disjonctions.

Dans notre cas, on pourrait choisir une voie intermédiaire entre celle de BCDR et de Cui, et qui correspondrait à la prise de l'intersection à la place de l'union, aussi bien pour les choix incontrôlables que pour les choix contrôlables. Cela simplifie grandement les choses (on aurait pas de disjonctions complexes à gérer - en plus de celles des contraintes de résolution de conflit) et pourrait réutiliser les mêmes variables (pour les durées incontrôlables "communes" à différents scénarios) dans les programmes linéaires permettant de résoudre les conflits et/ou relaxer des durées incontrôlables. Enfin, cela ferait aussi sens par rapport à notre paradigme de construction incrémentelle d'un plan conditionnel / contingent.

Notons toutefois que le fait de "forcer" (à chaque ajout incrémentel de scénario(s?)) à restreindre / resserrer des durées contrôlables (tant que cela ne reste cohérent avec les autres contraintes...), justement afin que différents temps de dispatching d'un évènement ne pas rendre incontrollabile un des scénarios "empruntables" après. Ces "resserages" correspondraient alors à des conditions plus fortes que les conditions à observer de Cui. Mais elles pourraient présenter un compromis intéressant et quand même assez utile en pratique aussi.




**Notes sur les stratégies / politiques d'exécution dynamiques**

        La plupart des travaux sur la controllabilité dynamique et / ou les stratégies / poltiiques dynamiques abordent des problèmes ou seule l'incertitude temporelle est présente. Le plus souvent, l'incertitude temporelle est représentée via des STNUs, avec des durées incontrôllables comprises dans un intervalle. Dans les PSTN, des distributions de probabilité sont utilisées à la place d'intervalles. Pour aborder ces cas, on peut aborder un "degré de controllabilité dynamique" et l'évaluer avec de la MCTS, en simulant le dispatching du PSTN, ou bien "relaxer" le PSTN en un STNU par une approche d'allocation de risque. L'idée de cette dernière est de "relaxer" / approximer le PSTN en un STNU, avec des bornes sur les distributions de probabilités décrivant les durées, telle que la masse totale de probabilité en dehors de ces bornes soit inférieure à une certaine limite / risque.

        Dans les quelques travaux où les réseaux temporels incluent des "alternatives" ou des "choix", l'approche suivie le plus souvent peut être décrite comme dynamique temporellement, mais statique / forte non-temporellement. Il n'y a qu'un travail où que la controllabilité dynamique "totale" est considérée (i.e. temporelle et non-temporelle) [X]. Il y a aussi 3 hypothèses qui y sont faites. De notre point de vue, c'est la 3ème qui est la plus gênante - mais il semble qu'elle puisse être addressée assez tranquillement (du moins, on espère). Par ailleurs, ce travail ne traîte de durées incontrôllables représentées par des intervalles.

**Approche proposée (description informelle)**:

Notre idée est donc de construire petit à petit / incrémentellement / de façon anytime un plan conditionnel / contingent / arbre de scénarios (bdd/mdd?).

Précisons que ce plan n'est pas (complètement) une stratégie / politique d'exécution, parce qu'il ne considère pas explicitement les décisions / choix temporels / de scheduling / de dispatching.

L'idée est de construire petit à petit ce plan conditionnel à partir / en analysant des solutions "complètes" (y compris sur des variables aléatoires / incontrôlables) trouvées par le solveur / Aries, qu'on peut voir comme un "conseiller" / "fournisseur" de candidats (comme en recherche locale). L'idée est de traiter ces solutions en essayant de déterminer si cette solution peut être "étendue", çad s'il existe d'autres solutions valables avec les mêmes valeurs de variables contrôlables non-temporelles (idée à rapprocher des algos de recherche locale: considération de candidats dans le voisinage de la solution actuelle). Dans le cas contraire, on peut aussi considérer des nouveaux candidats avec une autre valeur pour une (ou plusieurs) variable contrôlable. 

Cela devra s'accompagner / être intercalé avec des idées similaires à celui de Cui [2], Wang [3] et peut-être même Levine [4]. Dans ce plan conditionnel, les variables devront être ordonnées totalement, dans un "ordre de pire cas": .... Ajoutons tout de même, que si on introduisant des variables supplémentaires pour observer et différencier des ordres différents (là où il pourrait y avoir ambiguité), alors on pourrait aussi représenter d'autres situations que celle de "pire cas". Dans l'arbre / graphe représentant le plan, il faudra associer des "DC-enveloppes" aux noeuds et arcs, qu'il faudra aussi combiner, "de bas en haut" [2]. Dans [2], seul le cas des durées incontrôlables représentées par un intervalle est considéré. Il faudra donc combiner / intercaler cela avec l'approche de relaxation / allocation de risque de [3]. Enfin, il faudra s'aider de l'algo [5] de DC-checking amélioré (incrémentel pour les relaxations). Enfin, il faudra aussi gérer un peu différemment (dans la combinaison des enveloppes) les noeuds correspondants aux variables contrôlables et incontrôlables. Il faudra aussi associer aux arcs (en particulier issus de noeuds correspondant aux variables incontrôlables) des poids correspondant à la probabilité de la (les?) valeur correspondant à l'arc. Des idées de [4] pourraient servir ici.

A terme, il serait même possible d'incorporer du backtracking dans le tableau final (en utilisant Aries / le solveur sat, pourquoi pas!).

Le principal point d'interrogation actuellement reste celui de comment déterminer efficacement les durées incontrôlables "pertinentes" (relevant) pour chaque contrainte molle, et de "quand" (dans l'arbre / graphe) et "de combien" les relaxer. En effet, ce serait mieux de voir ces relaxations comme des décisions / choix. Il faudrait aussi voir exactement comment gérer / modifier les seuils de risque des contraintes molles. En effet, il faudrait très certainement les "réequilibrer" en divisant `delta_i` par la masse de probabilité de la relaxation. Enfin, on pourrait aussi faire toutes les relaxations en amont, ce qui introduire un peu d'incomplétude, qu'on pourrait considérer comme acceptable, en laissant aux approches réactives / replanification / réparation de gérer les situations sortant de ces relaxations.

**Approche proposée (description informelle)**:

(2e tentative)

Notre idée est donc de construire petit à petit / incrémentellement / de façon anytime un plan conditionnel / contingent / arbre de scénarios (bdd/mdd?).

Précisons que ce plan n'est pas (complètement) une stratégie / politique d'exécution, parce qu'il ne considère pas explicitement les décisions / choix temporels / de scheduling / de dispatching.

Les principaux "ingrédients" qu'on souhaiterait utiliser / combiner / étendre:
- Les "DC-enveloppes" [2];
- Les relaxations de durées probabilistes en intervalles / allocation de risque [3];
- L'algorithme incrémentel pour ces relaxations [4];
- Calcul et représentation de probabilités conditionnelles, efficacement (+ représentation du plan conditionnel: utilisation d'un BDD / MDD à la place d'un arbre) [5].
