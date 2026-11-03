# elpiDiff : première journée de sprint

## 1. La preuve formelle

elpiDiff prend un programme qui calcule une fonction et produit deux
nouveaux programmes : le mode **tangent** et le mode **adjoint**. La preuve
formelle, faite en Rocq, montre que ces deux programmes calculent bien ce
qu'ils doivent calculer. Cette section explique ce qu'ils calculent.

### Le cadre

On prend une fonction $`f : \mathbb{R}^n \to \mathbb{R}^m`$, avec toutes les
bonnes conditions (dérivabilité, ...) : $`n`$ entrées, $`m`$ sorties.

- $`f(x)`$ est l'évaluation de $`f`$ au point $`x \in \mathbb{R}^n`$ ; c'est un
  vecteur de $`\mathbb{R}^m`$.
- $`\dfrac{df}{dx_j}(x)`$ est la dérivée de $`f`$ par rapport à
  la $`j`$-ième coordonnée, évaluée en $`x`$ ; c'est aussi un vecteur de
  $`\mathbb{R}^m`$ : comment **toutes les sorties** bougent quand on fait
  bouger **la seule entrée** $`j`$.
- On écrit $`f = (f_1, \dots, f_m)`$ : chaque $`f_i : \mathbb{R}^n \to \mathbb{R}`$
  est une des sorties de $`f`$. Son gradient est le vecteur de $`\mathbb{R}^n`$

$$\nabla f_i(x) = \left(\frac{df_i}{dx_1}(x), \dots, \frac{df_i}{dx_n}(x)\right) :$$

  comment **la seule sortie** $`i`$ bouge quand on fait bouger **chacune des
  entrées**.

Ces deux objets se lisent dans la jacobienne $`J_f(x)`$, la matrice
$`m \times n`$ de coefficients $`J_{ij} = \dfrac{df_i}{dx_j}(x)`$ :

- la **colonne** $`j`$ ($`m`$ coefficients) est $`\dfrac{df}{dx_j}(x)`$ ;
- la **ligne** $`i`$ ($`n`$ coefficients) est $`\nabla f_i(x)`$.

Le même coefficient se lit donc de deux façons :
$`\bigl(\nabla f_i(x)\bigr)_j = \left(\dfrac{df}{dx_j}(x)\right)_i = J_{ij}`$.

### Le mode tangent

Le mode tangent, tel qu'il est décrit en Elpi, construit une fonction

$$f_{\mathit{fwd}}(x, \mathit{sx}) = \mathit{sy}$$

- $`x \in \mathbb{R}^n`$ : le point où l'on dérive ;
- $`\mathit{sx} \in \mathbb{R}^n`$ : la graine (*seed*), une direction dans l'espace
  des entrées ;
- $`\mathit{sy} \in \mathbb{R}^m`$ : le résultat, dans l'espace des sorties.

$`\mathit{sy}`$ est la dérivée de $`f`$ en $`x`$ appliquée à $`\mathit{sx}`$, c'est-à-dire
$`\mathit{sy} = J_f(x)\, \mathit{sx}`$. C'est une combinaison des **colonnes** :

$$\mathit{sy} = \sum_{j=1}^{n} \mathit{sx}_j \, \frac{df}{dx_j}(x)$$

et, composante par composante,

$$\mathit{sy}_i = \langle \nabla f_i(x), \mathit{sx} \rangle .$$

Avec $`\mathit{sx} = e_j`$ (le $`j`$-ième vecteur de base), on obtient
$`\mathit{sy} = \dfrac{df}{dx_j}(x)`$ : **une exécution donne une
colonne**. Il faut donc $`n`$ exécutions pour avoir toute la jacobienne.

### Le mode adjoint

Le mode adjoint construit une fonction

$$f_{\mathit{adj}}(x, \mathit{sy}) = \mathit{sx}$$

- $`x \in \mathbb{R}^n`$ : le point où l'on dérive ;
- $`\mathit{sy} \in \mathbb{R}^m`$ : la graine, maintenant du côté des **sorties** ;
- $`\mathit{sx} \in \mathbb{R}^n`$ : le résultat, dans l'espace des **entrées**.

$`\mathit{sx}`$ est la transposée de la dérivée appliquée à $`\mathit{sy}`$, c'est-à-dire
$`\mathit{sx} = J_f(x)^{T} \mathit{sy}`$. C'est une combinaison des **lignes** :

$$\mathit{sx} = \sum_{i=1}^{m} \mathit{sy}_i \, \nabla f_i(x)$$

et, composante par composante,

$$\mathit{sx}_j = \left\langle \frac{df}{dx_j}(x), \mathit{sy} \right\rangle .$$

Avec $`\mathit{sy} = e_i`$, on obtient $`\mathit{sx} = \nabla f_i(x)`$, le gradient de la
$`i`$-ième sortie : **une exécution donne une ligne**. Pour une fonction à une
seule sortie ($`m = 1`$, le cas d'une fonction de coût), une seule exécution
donne tout le gradient.

### Les deux modes côte à côte

| mode | combinaison de | composante par composante | une exécution avec un vecteur de base donne |
|---|---|---|---|
| tangent | colonnes : $`\mathit{sy} = \sum_j \mathit{sx}_j \, \frac{df}{dx_j}(x)`$ | $`\mathit{sy}_i = \langle \nabla f_i(x), \mathit{sx} \rangle`$ | une colonne $`\frac{df}{dx_j}(x)`$ |
| adjoint | lignes : $`\mathit{sx} = \sum_i \mathit{sy}_i \, \nabla f_i(x)`$ | $`\mathit{sx}_j = \langle \frac{df}{dx_j}(x), \mathit{sy} \rangle`$ | une ligne $`\nabla f_i(x)`$ |

### Le lien entre les deux modes, sans la jacobienne

On peut relier les deux modes sans parler de la jacobienne. Pour toute
direction $`d \in \mathbb{R}^n`$ :

$$\langle f_{\mathit{fwd}}(x, d), \mathit{sy} \rangle = \langle d, f_{\mathit{adj}}(x, \mathit{sy}) \rangle .$$

Le produit scalaire de gauche est dans $`\mathbb{R}^m`$, celui de droite dans
$`\mathbb{R}^n`$. C'est le sens du mot « adjoint » : $`f_{\mathit{adj}}(x, \cdot)`$
est l'application adjointe (la transposée) de l'application linéaire
$`f_{\mathit{fwd}}(x, \cdot)`$.

On écrit $`d`$, et non $`\mathit{sx}`$, pour ne pas mélanger les noms : $`\mathit{sx}`$ est déjà
le nom du résultat de $`f_{\mathit{adj}}`$, et $`\mathit{sy}`$ celui du résultat de
$`f_{\mathit{fwd}}`$.

**L'intuition.**

- $`d`$ est un petit déplacement de l'entrée, de $`x`$ à $`x + \varepsilon d`$.
  Le mode tangent dit comment la sortie bouge :
  $`f(x + \varepsilon d) \approx f(x) + \varepsilon \, f_{\mathit{fwd}}(x, d)`$.
- La graine $`\mathit{sy}`$ est une pondération des sorties : elle transforme le
  vecteur des sorties en un seul nombre, $`L(y) = \langle \mathit{sy}, y \rangle`$
  (par exemple $`\mathit{sy} = e_i`$ choisit la $`i`$-ième sortie). Quand l'entrée bouge
  de $`\varepsilon d`$, ce nombre bouge d'environ
  $`\varepsilon \, \langle f_{\mathit{fwd}}(x, d), \mathit{sy} \rangle`$ : c'est le
  membre de gauche.
- Le résultat de l'adjoint, $`\mathit{sx} = f_{\mathit{adj}}(x, \mathit{sy})`$, répond à la
  même question **pour toutes les directions $`d`$ à la fois** : ce nombre
  bouge aussi de $`\varepsilon \, \langle d, \mathit{sx} \rangle`$. Autrement dit,
  $`\mathit{sx}`$ est le gradient du nombre $`L(f(x))`$ : il dit à quel point la sortie
  pondérée est sensible à chaque entrée.

Comme l'égalité vaut pour tout $`d`$, elle détermine complètement
$`f_{\mathit{adj}}`$ : avec $`d = e_j`$, la $`j`$-ième composante de
$`f_{\mathit{adj}}(x, \mathit{sy})`$ est $`\langle f_{\mathit{fwd}}(x, e_j), \mathit{sy} \rangle`$.
Avec les deux graines sur des vecteurs de base :
$`\bigl(f_{\mathit{adj}}(x, e_i)\bigr)_j = \bigl(f_{\mathit{fwd}}(x, e_j)\bigr)_i`$.

### Ce qui est prouvé en Rocq, et le lien avec ce qui précède

Les énoncés sont dans `rocq/top/Main.v` (et `rocq/top/MainMx.v` pour la
forme avec la jacobienne). Voici comment chaque objet mathématique des
sections précédentes apparaît en Rocq.

**$`f`$ est un programme.** En Rocq, `f` n'est pas une fonction de
$`\mathbb{R}^n`$ dans $`\mathbb{R}^m`$ : c'est un programme du langage d'entrée
d'elpiDiff, et ses arguments `x` sont une liste de valeurs (des réels, des
tableaux de réels). On retrouve la fonction mathématique en mettant bout à
bout tous les réels des arguments :

- $`n`$ est `in_dim x`, le nombre de réels des arguments, et le point
  $`x \in \mathbb{R}^n`$ est `point_of x` ;
- $`m`$ est `out_dim f x`, le nombre de réels du résultat ;
- la fonction $`f : \mathbb{R}^n \to \mathbb{R}^m`$ est `value_of f x` : on
  remplace les réels des arguments par ceux d'un vecteur de
  $`\mathbb{R}^n`$, on exécute le programme, on lit les réels du résultat.
  `value f x` est la valeur $`f(x)`$.

**Les « bonnes conditions ».** Elles ne sont pas supposées : elles sont
déduites de `accepted f x`, qui dit que elpiDiff accepte le programme (il
est bien formé), que les arguments ont la forme déclarée, et que le
programme est défini autour de $`x`$ (il n'utilise que des opérations
dérivables, là où elles le sont). Le théorème `derivative_exists` montre
qu'un programme accepté a une dérivée en $`x`$.

**La dérivée.** `derivative f x df` dit que `df` est la dérivée de $`f`$ en
$`x`$ : l'application linéaire de $`\mathbb{R}^n`$ dans $`\mathbb{R}^m`$ qui envoie
une direction $`\mathit{sx}`$ sur $`J_f(x)\,\mathit{sx} = \sum_j \mathit{sx}_j \, \frac{df}{dx_j}(x)`$. Avec un vecteur de base,
`D f x df (e x j)` est la colonne $`\frac{df}{dx_j}(x)`$.

**Une différence : les entrées dérivées.** Les arguments d'un programme ont
un rôle. On ne dérive que par rapport aux arguments indépendants (et aux
arguments `inout`) ; les autres (passifs ou dépendants) sont des constantes.
`seed dx` remplace par 0 les composantes de la direction `dx` qui tombent
sur ces arguments. Partout où on avait $`\mathit{sx}`$ (ou $`d`$), Rocq a donc
`seed dx`, et `D f x df dx` est $`J_f(x)`$ appliquée à `seed dx`.

**Le mode tangent : `tangent_correct`.** `run_tangent f x dx` exécute le
programme tangent produit par elpiDiff. Le théorème dit

    run_tangent f x dx = Some (f(x), D f x df dx)

c'est-à-dire $`f_{\mathit{fwd}}(x, \mathit{sx}) = \mathit{sy}`$ avec
$`\mathit{sy} = J_f(x)\,\mathit{sx}`$, exactement la section « Le mode
tangent ». Le programme rend aussi la valeur $`f(x)`$.

**Le mode adjoint : `adjoint_correct`.** `run_adjoint cv f x xb yb` exécute
le programme adjoint ; `yb` est la graine $`\mathit{sy}`$ et le résultat `g`
est $`\mathit{sx} = f_{\mathit{adj}}(x, \mathit{sy})`$. Le théorème dit, pour
toute direction `dx`,

    ⟨D f x df dx, yb⟩ = ⟨seed dx, g⟩

c'est exactement l'égalité de la section « Le lien entre les deux modes »,
$`\langle f_{\mathit{fwd}}(x, d), \mathit{sy} \rangle = \langle d, f_{\mathit{adj}}(x, \mathit{sy}) \rangle`$, avec $`d`$ = `seed dx`.
Deux paramètres en plus :

- `xb` : le programme adjoint ajoute ses résultats à des valeurs de départ
  `xb` ; `g` est ce qui a été ajouté, donc le théorème vaut quel que soit
  `xb` ;
- `cv` : choisit entre le mode adjoint seul et le mode qui rend aussi la
  valeur (*adjoint-value*) ; le théorème vaut pour les deux.
  `adjoint_value_correct` dit que la valeur rendue est bien $`f(x)`$ (sauf
  si le programme écrit dans un argument `inout`).

**Composante par composante : `adjoint_componentwise` et
`adjoint_jacobian`.** Pour toute entrée $`j`$ par rapport à laquelle on
dérive,

    nth j g = ⟨D f x df (e x j), yb⟩

c'est $`\mathit{sx}_j = \left\langle \frac{df}{dx_j}(x), \mathit{sy} \right\rangle`$ de la section « Le mode adjoint ». `adjoint_jacobian`
(`MainMx.v`) écrit la même chose avec la jacobienne,
$`g_j = \sum_i yb_i \, J_{ij}`$, c'est-à-dire $`\mathit{sx} = J_f(x)^T \mathit{sy}`$.

**Les deux programmes entre eux : `modes_agree`.** Avec `w` le résultat de
`run_tangent f x dx` et `g` celui de `run_adjoint f x xb yb`,

    ⟨w, yb⟩ = ⟨seed dx, g⟩

C'est l'égalité du lien écrite directement entre les deux programmes, sans
passer par la dérivée : ses hypothèses ne demandent pas `derivative`.

| section | objet mathématique | en Rocq |
|---|---|---|
| Le cadre | $`x \in \mathbb{R}^n`$, $`f(x) \in \mathbb{R}^m`$ | `point_of x`, `in_dim x`, `out_dim f x`, `value f x` |
| Le cadre | les bonnes conditions | `accepted f x` (puis `derivative_exists`) |
| Le cadre | $`\frac{df}{dx_j}(x)`$, $`J_f(x)`$ | `D f x df (e x j)`, `J f x df` |
| Le mode tangent | $`f_{\mathit{fwd}}(x, \mathit{sx}) = J_f(x)\,\mathit{sx}`$ | `tangent_correct` |
| Le mode adjoint | $`\mathit{sx}_j = \langle \frac{df}{dx_j}(x), \mathit{sy} \rangle`$ | `adjoint_componentwise`, `adjoint_jacobian` |
| Le lien | $`\langle f_{\mathit{fwd}}(x, d), \mathit{sy} \rangle = \langle d, f_{\mathit{adj}}(x, \mathit{sy}) \rangle`$ | `adjoint_correct`, `modes_agree` |

## 2. Un programme typique : un maillage qui évolue dans le temps

### Le programme

Un programme typique part d'un maillage dont les points évoluent dans le
temps. Il fait $`N`$ itérations en temps ; chaque itération met à jour tous
les éléments du maillage. À la fin, il calcule une seule valeur, par exemple
une énergie.

Avec les notations de la section 1 :

- l'**état** est le maillage, $`u \in \mathbb{R}^p`$ (les positions des
  points, éventuellement leurs vitesses) ;
- la **boucle en temps** calcule $`u_0 \to u_1 \to \dots \to u_N`$, avec
  $`u_{t+1} = \Phi(u_t)`$ : un pas de temps $`\Phi`$ met à jour tout le
  maillage ;
- le **résultat** est un seul nombre, l'énergie $`E = J(u_N)`$.

C'est donc une fonction $`f : \mathbb{R}^n \to \mathbb{R}`$, avec
$`x = u_0`$ (ou les paramètres de la simulation) et une seule sortie,
$`m = 1`$. Ce qu'on veut est le gradient $`\nabla E`$ : à quel point
l'énergie est sensible à chaque entrée.

### Pourquoi le mode adjoint

- En mode **tangent**, une exécution donne une seule dérivée
  $`\frac{dE}{dx_j}`$ : il faut $`n`$ exécutions, chacune coûtant une
  simulation entière.
- En mode **adjoint**, une seule exécution avec la graine
  $`\mathit{sy} = 1`$ donne tout le gradient $`\nabla E`$ : la jacobienne
  n'a qu'une ligne, et « une exécution donne une ligne » (section 1).

Le prix de l'adjoint est la mémoire. Le balayage arrière va du pas $`N`$ au
pas $`0`$ et a besoin des états $`u_t`$ dans l'ordre inverse. Il faut donc
les stocker pendant le balayage avant (la *tape*), jusqu'à $`N \times p`$
réels, ou bien les recalculer.

Dans elpiDiff, cette boucle en temps est un `fold` dont l'état est le
maillage, un tableau modifié en place : c'est le cas prouvé dans les étapes
« fold en place » de la preuve (M5, M5b).

### La trajectoire comme points de reprise

Souvent, le code garde déjà une version discrète de l'évolution, la
**trajectoire** : il sauve l'état tous les $`k`$ pas,
$`u_0, u_k, u_{2k}, \dots`$ Ces états sauvés sont exactement ce qu'il faut
pour des **points de reprise** (*checkpointing*) dans l'adjoint.

L'adjoint remonte le temps segment par segment, du dernier au premier. Pour
chaque segment $`[sk, (s+1)k]`$ :

1. il repart de l'état sauvé $`u_{sk}`$ et recalcule en avant les $`k`$ pas
   du segment, en gardant leurs états ;
2. il fait le balayage arrière sur ces $`k`$ pas.

Le schéma du code, avec $`N = S \cdot k`$. `step` est un pas de temps
$`u \mapsto \Phi(u)`$, `step_adj(u, ub)` son adjoint en $`u`$, et
`energy_adj(u, eb)` l'adjoint de l'énergie :

```text
// le programme : N pas, la trajectoire sauvée tous les k pas
function simulate(u0):
    u = u0
    for s in 0 .. S-1:
        traj[s] = u                    // point de reprise : l'état au pas s*k
        for i in 0 .. k-1:
            u = step(u)
    return energy(u), traj

// l'adjoint avec points de reprise : le gradient de l'énergie par rapport à u0
function simulate_adj(u0):
    E, traj = simulate(u0)             // balayage avant, ne garde que traj
    ub = energy_adj(u_N, 1)            // graine sy = 1 sur l'énergie
                                       // (u_N : l'état final, gardé par simulate)
    for s in S-1 down to 0:            // les segments, le dernier d'abord
        // 1. recalculer le segment depuis son point de reprise, en gardant chaque état
        u = traj[s]
        for i in 0 .. k-1:
            local[i] = u
            u = step(u)
        // 2. balayage arrière sur le segment, avec les états de local
        for i in k-1 down to 0:
            ub = step_adj(local[i], ub)
    return E, ub                       // ub = ∇E(u0)
```

**Ce que ça coûte.**

- **Mémoire** : `traj` ($`S`$ états) plus `local` ($`k`$ états), au lieu de
  $`N`$ états. Avec $`k \approx \sqrt{N}`$, environ $`2\sqrt{N}`$ états au
  lieu de $`N`$.
- **Temps** : les pas sont exécutés deux fois (dans `simulate`, puis au
  recalcul de chaque segment), plus un balayage adjoint : environ une
  simulation de plus.
- Si le programme garde déjà sa trajectoire pour ses propres besoins, les
  points de reprise sont gratuits.
- Si les pas dépendent de paramètres $`\theta`$, `step_adj` accumule aussi
  leur adjoint, $`\bar\theta \mathrel{+}= \dots`$, à chaque pas.
- Si $`k`$ ne divise pas $`N`$, le dernier segment est plus court ; le code
  ne change pas.

L'algorithme *revolve* de Griewank est la version optimale de cette idée,
avec des points de reprise placés récursivement.

**Où en est elpiDiff.** Aujourd'hui, l'adjoint d'elpiDiff stocke à chaque
pas ce que l'analyse *to-be-recorded* demande (la *tape*), sans points de
reprise. Dans le schéma ci-dessus, seule la phase 2 correspond à ce que
l'adjoint produit aujourd'hui ; la phase 1, et le découpage de la boucle en
deux boucles imbriquées (segments × $`k`$ pas), seraient nouveaux.

## 3. Rendre L0 interprocédural

### Ce que L0 sait faire aujourd'hui

Aujourd'hui, L0 décrit **une seule fonction** : des arguments, chacun avec
un rôle, puis un corps fait de `let`, `ite`, `map`, `fold`, `get`/`set` et
d'opérations élémentaires. Les seuls appels sont des appels à ces opérations
(`sin`, `exp`, `*`, …), dont on connaît les dérivées partielles. Les
interfaces C++ et Julia traduisent tout autre appel d'une fonction d'un réel
en `unknown1 "g"`, qu'on ne sait pas dériver. Avec plusieurs fonctions
Julia, chacune est dérivée séparément : elles ne s'appellent jamais.

### Ce qui manque

1. **Le langage.** Un programme devient une liste de fonctions, avec une
   construction `call g args`. Comme `g` peut écrire dans ses arguments
   (rôles `dependent` et `inout`), un appel, dans le style fonctionnel de
   L0, doit rendre la valeur **et** les nouvelles versions des tableaux
   écrits, comme `set` le fait déjà pour un tableau.
2. **Les vérifications.**
   - Les arguments d'un appel doivent correspondre à la signature de `g`.
   - Le graphe des appels ne doit pas boucler (pas de récursion, au moins
     au début).
   - Un même tableau ne doit pas être passé deux fois à des arguments que
     `g` écrit (pas d'alias).
3. **Les évaluateurs et la passe ANF** : un cas pour l'appel.
4. **Les analyses deviennent interprocédurales.**
   - L'analyse d'activité et l'analyse *to-be-recorded* ont besoin d'un
     résumé de `g` : quelles sorties dépendent de quelles entrées, ce que
     son adjoint lit, ce qu'il écrase.
   - Les rôles des arguments de `g` dépendent de l'endroit de l'appel : une
     même fonction `g` peut demander plusieurs versions dérivées, une par
     choix des arguments actifs.
5. **Comment dériver un appel.** Deux stratégies :
   - **Déplier `g` avant de dériver** (*inlining*). Tout le reste ne change
     pas, et la preuve demande seulement que le dépliage garde le sens du
     programme. Le prix : la taille du code, et pas de dérivée séparée de
     `g`. C'est la première étape naturelle.
   - **Une dérivée par fonction.**
     - Le tangent est simple : `call g` devient `call g_tangent` (la valeur
       et la tangente).
     - L'adjoint est plus difficile. Soit l'adjoint de `g` recalcule son
       propre balayage avant à partir des entrées sauvées : ce sont les
       points de reprise de la section 2, à la frontière de l'appel. Soit
       on coupe `g` en deux, `g_fwd`, qui stocke sa *tape*, et `g_rev`, qui
       l'utilise : le « mode séparé » (*split mode*).
6. **Les générateurs de code** : C++ et Julia écrivent plusieurs fonctions
   et les appels entre elles.
7. **Rocq.** La sémantique des appels, puis un cas « appel » dans les
   preuves : le théorème déjà prouvé pour `g` sert d'hypothèse à chaque
   appel (c'est la règle de dérivation des fonctions composées), par
   récurrence sur le graphe des appels.

### Dans quel ordre

1. Le langage, les vérifications et les évaluateurs.
2. Le dépliage : tout marche, sans rien changer à la dérivation.
3. Le tangent par fonction.
4. L'adjoint par fonction : d'abord en recalculant, ensuite en mode séparé.

Rocq suit à chaque étape.
