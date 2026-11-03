# elpiDiff : première journée de sprint

## 1. La preuve formelle

elpiDiff prend un programme qui calcule une fonction et produit deux
nouveaux programmes : le mode **tangent** et le mode **adjoint**. La preuve
formelle, faite en Rocq, montre que ces deux programmes calculent bien ce
qu'ils doivent calculer. Cette section explique ce qu'ils calculent.

### Le cadre

On prend une fonction $f : \mathbb{R}^m \to \mathbb{R}^n$, avec toutes les
bonnes conditions (dérivabilité, ...) : $m$ entrées, $n$ sorties.

- $f(x)$ est l'évaluation de $f$ au point $x \in \mathbb{R}^m$ ; c'est un
  vecteur de $\mathbb{R}^n$.
- $\dfrac{df}{dx_j}(x)$ est la dérivée de $f$ par rapport à
  la $j$-ième coordonnée, évaluée en $x$ ; c'est aussi un vecteur de
  $\mathbb{R}^n$ : comment **toutes les sorties** bougent quand on fait
  bouger **la seule entrée** $j$.
- On écrit $f = (f_1, \dots, f_n)$ : chaque $f_i : \mathbb{R}^m \to \mathbb{R}$
  est une des sorties de $f$. Son gradient est le vecteur de $\mathbb{R}^m$
  $$\nabla f_i(x) = \left(\frac{df_i}{dx_1}(x), \dots,
  \frac{df_i}{dx_m}(x)\right) :$$
  comment **la seule sortie** $i$ bouge quand on fait bouger **chacune des
  entrées**.

Ces deux objets se lisent dans la jacobienne $J_f(x)$, la matrice
$n \times m$ de coefficients $J_{ij} = \dfrac{df_i}{dx_j}(x)$ :

- la **colonne** $j$ ($n$ coefficients) est $\dfrac{df}{dx_j}(x)$ ;
- la **ligne** $i$ ($m$ coefficients) est $\nabla f_i(x)$.

Le même coefficient se lit donc de deux façons :
$\bigl(\nabla f_i(x)\bigr)_j = \left(\dfrac{df}{dx_j}(x)\right)_i = J_{ij}$.

### Le mode tangent

Le mode tangent, tel qu'il est décrit en Elpi, construit une fonction

$$f_{\mathit{fwd}}(x, \mathit{sx}) = \mathit{sy}$$

- $x \in \mathbb{R}^m$ : le point où l'on dérive ;
- $\mathit{sx} \in \mathbb{R}^m$ : la graine (*seed*), une direction dans l'espace
  des entrées ;
- $\mathit{sy} \in \mathbb{R}^n$ : le résultat, dans l'espace des sorties.

$\mathit{sy}$ est la dérivée de $f$ en $x$ appliquée à $\mathit{sx}$, c'est-à-dire
$\mathit{sy} = J_f(x)\, \mathit{sx}$. C'est une combinaison des **colonnes** :

$$\mathit{sy} = \sum_{j=1}^{m} \mathit{sx}_j \, \frac{df}{dx_j}(x)$$

et, composante par composante,

$$\mathit{sy}_i = \langle \nabla f_i(x), \mathit{sx} \rangle .$$

Avec $\mathit{sx} = e_j$ (le $j$-ième vecteur de base), on obtient
$\mathit{sy} = \dfrac{df}{dx_j}(x)$ : **une exécution donne une
colonne**. Il faut donc $m$ exécutions pour avoir toute la jacobienne.

### Le mode adjoint

Le mode adjoint construit une fonction

$$f_{\mathit{adj}}(x, \mathit{sy}) = \mathit{sx}$$

- $x \in \mathbb{R}^m$ : le point où l'on dérive ;
- $\mathit{sy} \in \mathbb{R}^n$ : la graine, maintenant du côté des **sorties** ;
- $\mathit{sx} \in \mathbb{R}^m$ : le résultat, dans l'espace des **entrées**.

$\mathit{sx}$ est la transposée de la dérivée appliquée à $\mathit{sy}$, c'est-à-dire
$\mathit{sx} = J_f(x)^{T} \mathit{sy}$. C'est une combinaison des **lignes** :

$$\mathit{sx} = \sum_{i=1}^{n} \mathit{sy}_i \, \nabla f_i(x)$$

et, composante par composante,

$$\mathit{sx}_j = \left\langle \frac{df}{dx_j}(x), \mathit{sy} \right\rangle .$$

Avec $\mathit{sy} = e_i$, on obtient $\mathit{sx} = \nabla f_i(x)$, le gradient de la
$i$-ième sortie : **une exécution donne une ligne**. Pour une fonction à une
seule sortie ($n = 1$, le cas d'une fonction de coût), une seule exécution
donne tout le gradient.

### Les deux modes côte à côte

| mode | combinaison de | composante par composante | une exécution avec un vecteur de base donne |
|---|---|---|---|
| tangent | colonnes : $\mathit{sy} = \sum_j \mathit{sx}_j \, \frac{df}{dx_j}(x)$ | $\mathit{sy}_i = \langle \nabla f_i(x), \mathit{sx} \rangle$ | une colonne $\frac{df}{dx_j}(x)$ |
| adjoint | lignes : $\mathit{sx} = \sum_i \mathit{sy}_i \, \nabla f_i(x)$ | $\mathit{sx}_j = \langle \frac{df}{dx_j}(x), \mathit{sy} \rangle$ | une ligne $\nabla f_i(x)$ |

### Le lien entre les deux modes, sans la jacobienne

On peut relier les deux modes sans parler de la jacobienne. Pour toute
direction $d \in \mathbb{R}^m$ :

$$\langle f_{\mathit{fwd}}(x, d), \mathit{sy} \rangle = \langle d, f_{\mathit{adj}}(x, \mathit{sy}) \rangle .$$

Le produit scalaire de gauche est dans $\mathbb{R}^n$, celui de droite dans
$\mathbb{R}^m$. C'est le sens du mot « adjoint » : $f_{\mathit{adj}}(x, \cdot)$
est l'application adjointe (la transposée) de l'application linéaire
$f_{\mathit{fwd}}(x, \cdot)$.

On écrit $d$, et non $\mathit{sx}$, pour ne pas mélanger les noms : $\mathit{sx}$ est déjà
le nom du résultat de $f_{\mathit{adj}}$, et $\mathit{sy}$ celui du résultat de
$f_{\mathit{fwd}}$.

**L'intuition.**

- $d$ est un petit déplacement de l'entrée, de $x$ à $x + \varepsilon d$.
  Le mode tangent dit comment la sortie bouge :
  $f(x + \varepsilon d) \approx f(x) + \varepsilon \, f_{\mathit{fwd}}(x, d)$.
- La graine $\mathit{sy}$ est une pondération des sorties : elle transforme le
  vecteur des sorties en un seul nombre, $L(y) = \langle \mathit{sy}, y \rangle$
  (par exemple $\mathit{sy} = e_i$ choisit la $i$-ième sortie). Quand l'entrée bouge
  de $\varepsilon d$, ce nombre bouge d'environ
  $\varepsilon \, \langle f_{\mathit{fwd}}(x, d), \mathit{sy} \rangle$ : c'est le
  membre de gauche.
- Le résultat de l'adjoint, $\mathit{sx} = f_{\mathit{adj}}(x, \mathit{sy})$, répond à la
  même question **pour toutes les directions $d$ à la fois** : ce nombre
  bouge aussi de $\varepsilon \, \langle d, \mathit{sx} \rangle$. Autrement dit,
  $\mathit{sx}$ est le gradient du nombre $L(f(x))$ : il dit à quel point la sortie
  pondérée est sensible à chaque entrée.

Comme l'égalité vaut pour tout $d$, elle détermine complètement
$f_{\mathit{adj}}$ : avec $d = e_j$, la $j$-ième composante de
$f_{\mathit{adj}}(x, \mathit{sy})$ est $\langle f_{\mathit{fwd}}(x, e_j), \mathit{sy} \rangle$.
Avec les deux graines sur des vecteurs de base :
$\bigl(f_{\mathit{adj}}(x, e_i)\bigr)_j = \bigl(f_{\mathit{fwd}}(x, e_j)\bigr)_i$.

### Ce qui est prouvé en Rocq

Les énoncés courts sont dans `top/Main.v` (et `top/MainMx.v` pour la forme
matricielle). Il n'y a pas d'`Admitted`. Les énoncés de `Main.v` utilisent
seulement les axiomes standard des réels de Rocq ; la forme matricielle
(`MainMx.v`) en ajoute un, `constructive_indefinite_description`, pour voir
les réels comme un anneau de MathComp.

- **`tangent_correct`** : le programme tangent calcule la valeur et la
  dérivée dans la direction donnée,

      run_tangent f x dx = Some (f(x), D f x df dx)

- **`adjoint_correct`** : le programme adjoint calcule l'adjoint de la
  dérivée, c'est l'égalité du lien ci-dessus,

      ⟨D f x df dx, yb⟩ = ⟨seed dx, g⟩      pour tout dx

  où `g` est le résultat de `run_adjoint` et `yb` la graine $\mathit{sy}$.
- **`adjoint_jacobian`** (`MainMx.v`) : la même chose composante par
  composante, $g_j = \sum_i yb_i \, J_{ij}$.
- **`modes_agree`** : les deux programmes vérifient l'égalité du lien,
  `⟨w, yb⟩ = ⟨seed dx, g⟩`, avec `w` le résultat de `run_tangent` et `g`
  celui de `run_adjoint`. Ses hypothèses ne parlent pas de dérivée : les
  deux modes sont d'accord même là où $f$ n'est pas dérivable.
