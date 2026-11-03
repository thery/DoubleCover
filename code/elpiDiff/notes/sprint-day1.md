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
- $\dfrac{\partial f}{\partial x_j}(x)$ est la dérivée de $f$ par rapport à
  la $j$-ième coordonnée, évaluée en $x$ ; c'est aussi un vecteur de
  $\mathbb{R}^n$ : comment **toutes les sorties** bougent quand on fait
  bouger **la seule entrée** $j$.
- On écrit $f = (f_1, \dots, f_n)$ : chaque $f_i : \mathbb{R}^m \to \mathbb{R}$
  est une des sorties de $f$. Son gradient est le vecteur de $\mathbb{R}^m$
  $$\nabla f_i(x) = \left(\frac{\partial f_i}{\partial x_1}(x), \dots,
  \frac{\partial f_i}{\partial x_m}(x)\right) :$$
  comment **la seule sortie** $i$ bouge quand on fait bouger **chacune des
  entrées**.

Ces deux objets se lisent dans la jacobienne $J_f(x)$, la matrice
$n \times m$ de coefficients $J_{ij} = \dfrac{\partial f_i}{\partial x_j}(x)$ :

- la **colonne** $j$ ($n$ coefficients) est $\dfrac{\partial f}{\partial x_j}(x)$ ;
- la **ligne** $i$ ($m$ coefficients) est $\nabla f_i(x)$.

Le même coefficient se lit donc de deux façons :
$\bigl(\nabla f_i(x)\bigr)_j = \left(\dfrac{\partial f}{\partial x_j}(x)\right)_i = J_{ij}$.

### Le mode tangent

Le mode tangent, tel qu'il est décrit en Elpi, construit une fonction

$$f_{\mathit{fwd}}(x, s_x) = s_y$$

- $x \in \mathbb{R}^m$ : le point où l'on dérive ;
- $s_x \in \mathbb{R}^m$ : la graine (*seed*), une direction dans l'espace
  des entrées ;
- $s_y \in \mathbb{R}^n$ : le résultat, dans l'espace des sorties.

$s_y$ est la dérivée de $f$ en $x$ appliquée à $s_x$, c'est-à-dire
$s_y = J_f(x)\, s_x$. C'est une combinaison des **colonnes** :

$$s_y = \sum_{j=1}^{m} s_{x,j} \, \frac{\partial f}{\partial x_j}(x),
\qquad\text{et, composante par composante,}\qquad
s_{y,i} = \langle \nabla f_i(x), s_x \rangle .$$

Avec $s_x = e_j$ (le $j$-ième vecteur de base), on obtient
$s_y = \dfrac{\partial f}{\partial x_j}(x)$ : **une exécution donne une
colonne**. Il faut donc $m$ exécutions pour avoir toute la jacobienne.

### Le mode adjoint

Le mode adjoint construit une fonction

$$f_{\mathit{adj}}(x, s_y) = s_x$$

- $x \in \mathbb{R}^m$ : le point où l'on dérive ;
- $s_y \in \mathbb{R}^n$ : la graine, maintenant du côté des **sorties** ;
- $s_x \in \mathbb{R}^m$ : le résultat, dans l'espace des **entrées**.

$s_x$ est la transposée de la dérivée appliquée à $s_y$, c'est-à-dire
$s_x = J_f(x)^{T} s_y$. C'est une combinaison des **lignes** :

$$s_x = \sum_{i=1}^{n} s_{y,i} \, \nabla f_i(x),
\qquad\text{et, composante par composante,}\qquad
s_{x,j} = \left\langle \frac{\partial f}{\partial x_j}(x), s_y \right\rangle .$$

Avec $s_y = e_i$, on obtient $s_x = \nabla f_i(x)$, le gradient de la
$i$-ième sortie : **une exécution donne une ligne**. Pour une fonction à une
seule sortie ($n = 1$, le cas d'une fonction de coût), une seule exécution
donne tout le gradient.

### Les deux modes côte à côte

| mode | combinaison de | composante par composante | une exécution avec un vecteur de base donne |
|---|---|---|---|
| tangent | colonnes : $s_y = \sum_j s_{x,j} \, \frac{\partial f}{\partial x_j}(x)$ | $s_{y,i} = \langle \nabla f_i(x), s_x \rangle$ | une colonne $\frac{\partial f}{\partial x_j}(x)$ |
| adjoint | lignes : $s_x = \sum_i s_{y,i} \, \nabla f_i(x)$ | $s_{x,j} = \langle \frac{\partial f}{\partial x_j}(x), s_y \rangle$ | une ligne $\nabla f_i(x)$ |

### Le lien entre les deux modes, sans la jacobienne

On peut relier les deux modes sans parler de la jacobienne. Pour toute
direction $d \in \mathbb{R}^m$ :

$$\langle f_{\mathit{fwd}}(x, d), s_y \rangle = \langle d, f_{\mathit{adj}}(x, s_y) \rangle .$$

Le produit scalaire de gauche est dans $\mathbb{R}^n$, celui de droite dans
$\mathbb{R}^m$. C'est le sens du mot « adjoint » : $f_{\mathit{adj}}(x, \cdot)$
est l'application adjointe (la transposée) de l'application linéaire
$f_{\mathit{fwd}}(x, \cdot)$.

On écrit $d$, et non $s_x$, pour ne pas mélanger les noms : $s_x$ est déjà
le nom du résultat de $f_{\mathit{adj}}$, et $s_y$ celui du résultat de
$f_{\mathit{fwd}}$.

**L'intuition.**

- $d$ est un petit déplacement de l'entrée, de $x$ à $x + \varepsilon d$.
  Le mode tangent dit comment la sortie bouge :
  $f(x + \varepsilon d) \approx f(x) + \varepsilon \, f_{\mathit{fwd}}(x, d)$.
- La graine $s_y$ est une pondération des sorties : elle transforme le
  vecteur des sorties en un seul nombre, $L(y) = \langle s_y, y \rangle$
  (par exemple $s_y = e_i$ choisit la $i$-ième sortie). Quand l'entrée bouge
  de $\varepsilon d$, ce nombre bouge d'environ
  $\varepsilon \, \langle f_{\mathit{fwd}}(x, d), s_y \rangle$ : c'est le
  membre de gauche.
- Le résultat de l'adjoint, $s_x = f_{\mathit{adj}}(x, s_y)$, répond à la
  même question **pour toutes les directions $d$ à la fois** : ce nombre
  bouge aussi de $\varepsilon \, \langle d, s_x \rangle$. Autrement dit,
  $s_x$ est le gradient du nombre $L(f(x))$ : il dit à quel point la sortie
  pondérée est sensible à chaque entrée.

Comme l'égalité vaut pour tout $d$, elle détermine complètement
$f_{\mathit{adj}}$ : avec $d = e_j$, la $j$-ième composante de
$f_{\mathit{adj}}(x, s_y)$ est $\langle f_{\mathit{fwd}}(x, e_j), s_y \rangle$.
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

  où `g` est le résultat de `run_adjoint` et `yb` la graine $s_y$.
- **`adjoint_jacobian`** (`MainMx.v`) : la même chose composante par
  composante, $g_j = \sum_i yb_i \, J_{ij}$.
- **`modes_agree`** : les deux programmes vérifient l'égalité du lien,
  `⟨w, yb⟩ = ⟨seed dx, g⟩`, avec `w` le résultat de `run_tangent` et `g`
  celui de `run_adjoint`. Ses hypothèses ne parlent pas de dérivée : les
  deux modes sont d'accord même là où $f$ n'est pas dérivable.
