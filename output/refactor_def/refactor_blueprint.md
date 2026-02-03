## Refactoring Blueprint summary

Your instruction file is **not** label-driven; it is **number-driven** (“Proposition 4.5”, “Notation 4.22”, “Paragraph 4.14”, etc.). I therefore:

1. **Parsed `paper.aux`** to map every printed number (e.g. `4.23`) to its internal LaTeX label (e.g. `P:increment of degrees in ghost series`).
2. **Located each block in `paper.tex`** by searching for the corresponding `\label{…}` (or, when missing, by bracketing the unlabeled environment near a later labeled item).
3. Produced a **Refactoring Table** with:
   **Label · Current Number · Action (Formalize / Do Not Formalize / Redefine) · First-sentence locator OR new-definition plan**.

The **key decoupling move** is to replace the representation-/geometry-dependent objects (e.g. the module (\widetilde{\rmH}), (\bar\rho), explicit (\GL_2)-representation computations) by **purely combinatorial parameters and functions**:

* Parameters: prime (p), integer (a) with (1\le a\le p-4), a cyclic group (\Delta\cong \mathbb F_p^\times), Teichmüller (\omega).
* Derived data from a “relevant character” (\varepsilon): integers (s_\varepsilon, k_\varepsilon, \delta_\varepsilon, t_1^{(\varepsilon)}, t_2^{(\varepsilon)}).
* **Dimension functions** (d_k^{\Iw}(\cdot)) and (d_k^{\unr}(\cdot)) are **redefined from Propositions 4.5 and 4.15 as definitions**, i.e. *axiomatized by their explicit floor formulas*.
* The **ghost series** is then **purely combinatorial**: built from those dimension functions and the multiplicity recipe.

---

## Redefinitions required by the instructions (exact math content to keep)

### (A) Redefine “relevant character” (from Notation 2.83) to remove (\widetilde{\rmH}), (\bar\rho)

**New definition text (to replace the rep-theoretic part of Notation 2.83):**

Fix prime (p) and (a\in{1,\dots,p-4}). Let (\Delta=\mathbb F_p^\times) and (\omega:\Delta\to\mathbb Z_p^\times) the Teichmüller character.
A **relevant character** of (\Delta^2) is a character
[
\varepsilon = \varepsilon_1\times \varepsilon_2
\quad\text{with}\quad
\varepsilon_1=\omega^{-s_\varepsilon},\ \varepsilon_2=\omega^{a+s_\varepsilon}
]
for some integer (s_\varepsilon) (taken modulo (p-1); pick the standard representative (0\le s_\varepsilon\le p-2)).
Define
[
k_\varepsilon \in{2,\dots,p}\ \text{by}\
k_\varepsilon \equiv a+2s_\varepsilon+2 \pmod{p-1}.
]

This is the “combinatorial core” actually used later (and explicitly invoked again in later sections), while the (\widetilde{\rmH})/(\bar\rho) motivation is dropped.

---

### (B) Redefine (d_k^{\Iw}) using Proposition 4.5 as a *definition* (no proof)

**New definition text:**
For relevant (\varepsilon=\omega^{-s_\varepsilon}\times\omega^{a+s_\varepsilon}) and integer (k\ge2),
[
d_k^{\Iw}!\big(\varepsilon\cdot(1\times\omega^{2-k})\big)
:= \Big\lfloor \frac{k-2-s_\varepsilon}{p-1}\Big\rfloor

* \Big\lfloor \frac{k-2-{a+s_\varepsilon}}{p-1}\Big\rfloor +2.
  ]
  (All later uses of Proposition 4.5 become “unfold the definition”.)

---

### (C) Redefine (d_k^{\unr}) using Proposition 4.15 as a *definition* (no proof)

After defining (k_\bullet) (Notation 4.6) and (t_1^{(\varepsilon)},t_2^{(\varepsilon)}) (Paragraph 4.14), define:
[
d_k^{\unr}(\varepsilon_1)
:= \Big\lfloor \frac{k_\bullet - t_1}{p+1}\Big\rfloor

* \Big\lfloor \frac{k_\bullet - t_2}{p+1}\Big\rfloor + 2.
  ]
  Ignore the representation-theoretic derivation in \S4.10 and ignore equation (4.11.1) as instructed.

---

### (D) Redefine the ghost series (Definition 2.84) to remove (\widetilde{\rmH})

**New definition text:**
Define (G^{(\varepsilon)}(w,t)=1+\sum_{n\ge1}g_n^{(\varepsilon)}(w)t^n) with
[
g_n^{(\varepsilon)}(w) := \prod_{\substack{k\ge2\ k\equiv k_\varepsilon\ (p-1)}} (w-w_k)^{m_n^{(\varepsilon)}(k)} \in \mathbb Z_p[w],
]
where the multiplicities are defined purely from (d^{\Iw}) and (d^{\unr}) by the piecewise “min” recipe appearing in the paper’s Definition 2.84.
You then **prove/record** the increment identities (2.84.3) and (2.84.4) about (m_n^{(\varepsilon)}(k)) as separate lemmas (since your instructions explicitly request them).

**Refactoring note for Lean:** treat the product as a **finite product** by proving that for fixed (n), only finitely many weights (k) have (m_n^{(\varepsilon)}(k)\ne0) (this is standard from the min-recipe + monotonicity of dimensions; if the paper already proves it implicitly, we isolate it as a lemma early).

---

### (E) Redefine “power basis” (Notation 3.17) to keep only degree bookkeeping

Keep only:

* degree function (\deg(\bfe)=j),
* an ordering (\bfe_1^{(\varepsilon)},\bfe_2^{(\varepsilon)},\dots) by strictly increasing degrees,
* definition of the “classical subset” (\bfB_k^{(\varepsilon)} = {\bfe: \deg(\bfe)\le k-2}).

Drop all (U_p)-matrix content and representation-theoretic construction of the basis.

---

## Refactoring Table for every instruction-mentioned item

### Table A — Direct items mentioned in `instruction.tex`

| Label                                                      | Current Number | Action           | Located Env | Locator Quote/Definition                                                                                                                                                                                                                                                                                    |
| ---------------------------------------------------------- | -------------- | ---------------- | ----------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| NEW:NewtonPolygon_general                                  |                | Redefine         |             | Generalize Notation 2.87 from $\CC_p$ to any non-archimedean valued field/ring; define Newton polygon as lower convex hull of points (n, v(f_n)) for a power series with f_0=1.                                                                                                                             |
| NEW:NewtonPolygon_mul_minkowski                            |                | Formalize        |             | Add lemma: NP(F*G) = NP(F) ⊕ NP(G) (Minkowski sum of polygons); use valuation property v((fg)*n)=min*{i+j=n} v(f_i)+v(g_j).                                                                                                                                                                                 |
| NEW:GlobalData_a_p_Delta_omega                             |                | Formalize        |             | Introduce parameters: prime p, integer a with 1≤a≤p-4, group Δ=F_p^×, Teichmüller character ω:Δ→Z_p^×, and basic residue notation {·} mod (p-1).                                                                                                                                                            |
| N:Newton polygon                                           | 2.87           | Redefine         | notation    | For a power series $F(t) = \sum_{n \geq 0} f_n t^n\in \CC_p\llbracket t\rrbracket$ (with $f_0=1$), we use $\NP(F)$ to denote its \emph{Newton polygon}, that is the convex hull of points $(n, v_p(f_n))$ for all $n$.                                                                                      |
| N:relevant varepsilon                                      | 2.83           | Redefine         | notation    | For the rest of this paper, we fix a \emph{primitive} $\calO\llbracket K_p\rrbracket$-projective augmented module $\widetilde \rmH$ of type $\bar \rho$, unless otherwise specified.                                                                                                                        |
| D:ghost series                                             | 2.84           | Redefine         | definition  | Following \cite{bergdall-pollack2,bergdall-pollack3}, we define the \emph{ghost series} for $\widetilde \rmH$ over $\calW^{(\varepsilon)}$ to be the formal power series $$ G^{(\var                                                                                                                        |
| E:increment of multiplicity                                | 2.84.3         | Formalize        | equation    | m_{n+1}^{(\varepsilon)}(k) -m_{n}^{(\varepsilon)}(k) = 1 & \textrm{ if } d_{k}^\unr(\varepsilon_1) \leq n< \frac 12 d_{k}^\Iw(\tilde \varepsilon_1) \ -1 & \tex                                                                                                                                             |
| E:second order increment of multiplicity                   | 2.84.4         | Formalize        | equation    | m_{n+1}^{(\varepsilon)}(k) -2m_n^{(\varepsilon)}(k) +m_{n-1}^{(\varepsilon)}(k) = -2 & \textrm{ if } n = \frac 12 d_{k}^\Iw(\tilde \varepsilon_1) \ 1 & \textrm                                                                                                                                             |
| N:power basis                                              | 3.17           | Redefine         | notation    | We call \eqref{E:basis of Sdagger} the \emph{power basis} of $\rmS^{\dagger, (\varepsilon)}$ and  $\rmS_{k}^{\dagger}\big(\varepsilon\cdot (1\times \omega^{2-k})\big)$, denoted by $\bfB^{ (\varepsilon)}$ (as it formally does not depend on $k$).                                                        |
| P:dimension of SIw                                         | 4.5            | Redefine         | proposition | We have the following dimension formulas d_{k}^\Iw\big(\varepsilon\cdot (1\times \omega^{2-k})\big) = \Big\lfloor \frac{k-2-s_\varepsilon}{p-1}\Big\rfloor + \Big\lfloor \frac{k-2-{a+s_\varepsilon}}{p-1}\Big\rfloor +2.                                                                                   |
| N:kbullet                                                  | 4.6            | Formalize        | notation    | For $\varepsilon$ relevant, we set $$ \delta_\varepsilon = \Big\lfloor \frac{s_\varepsilon + {a+s_\varepsilon}}{p-1}\Big \rfloor = \begin{cases} 0 & \textrm{ if }s_\varepsilon + {a+s_\varepsilon} < p-1,\ 1 & \textrm{ if }s_\varepsilon + {a+s_\varepsilon} \geq p-1. \end{cases} $$                     |
| C:dIw is even                                              | 4.8            | Formalize        | corollary   | When $k = k_\varepsilon + k_\bullet (p-1)$, we have $$ d_{k}^\Iw(\tilde \varepsilon_1) = 2k_\bullet +2 -2 \delta_\varepsilon.                                                                                                                                                                               |
| S:explicit Sunr                                            | 4.10           | Do Not Formalize |             | Representation-theoretic computation section; keep only downstream combinatorial definitions (t1,t2; d^unr).                                                                                                                                                                                                |
| E:dimension formula dkunr                                  | 4.11.1         | Do Not Formalize | equation    | d_{k}^\unr(\varepsilon_1) &=& \Big\lfloor \frac{k_\bullet - t_1}{p+1}\Big\rfloor + \Big\lfloor \frac{k_\bullet - t_2}{p+1}\Big\rfloor + 2 \ \nonumber &=& 2\Big\lfloor \frac{k_\bullet - t_1}{p                                                                                                             |
| P:para_127                                                 | 4.14           | Formalize        | para        | Using the notation above, we introduce two integers $t_1=t_1^{(\varepsilon)}$ and $t_2 =t_2^{(\varepsilon)}$ as follows: \item when $a+s_\varepsilon<p-1$, $t_1 = s_\varepsilon+\delta_\varepsilon$ and                                                                                                     |
| P:dimension of Sunr                                        | 4.15           | Redefine         | proposition | We have d_{k}^\unr(\varepsilon_1) &=& \Big\lfloor \frac{k_\bullet - t_1}{p+1}\Big\rfloor + \Big\lfloor \frac{k_\bullet - t_2}{p+1}\Big\rfloor + 2 \ \nonumber &=& 2\Big\lfloor \frac{k_\bullet - t_1}{p                                                                                                     |
| N:tnvarepsilon                                             | 4.22           | Formalize        | notation    | For $n \in \ZZ$ and $\varepsilon$ a relevant character, we set $\beta_{[n]}^{(\varepsilon)} = \begin{cases} t_1^{(\varepsilon)} & \textrm{if }n \textrm{ is even} \ t_2^{(\varepsilon)}- \tfrac{p+1}2 & \textrm{if }n \textrm{ is odd} \end{cases}$.                                                        |
| P:increment of degrees in ghost series                     | 4.23           | Formalize        | proposition | Fix $\varepsilon$ a relevant character.                                                                                                                                                                                                                                                                     |
| R:meaning of kmidminmax                                    | 4.27           | Formalize        | remark      | From the definition of $k_{\mathrm{mid}\bullet}^{(\varepsilon)}(n)$, $k_{\mathrm{min}\bullet}^{(\varepsilon)}(n)$, and $k^{(\varepsilon)}*{\mathrm{max} \bullet}(n)$, we see that \item $\frac 12d_k^\Iw(\tilde \varepsilon_1) = n \Leftrightarrow k*\bullet = k_{\mathrm{mid}\bullet}^{(\varepsilon)}(n)$. |
| C:ghost versus halo                                        | 4.28           | Do Not Formalize | corollary   | Let $k \equiv k_\varepsilon \bmod{p-1}$.                                                                                                                                                                                                                                                                    |
| N:gnhatk                                                   | 4.32           | Formalize        | notation    | For $k \equiv k_\varepsilon \bmod {(p-1)}$, we write $$ g^{(\varepsilon)}_{n,\hat k}(w): = g_n^{(\varepsilon)}(w) \big/ (w-w_k)^{m_n^{(\varepsilon)}(k)}.                                                                                                                                                   |
| P:ghost compatible with theta AL and p-stabilization_part1 | 4.34           | Formalize        | proposition | Fix $k_0 \geq 2$ and a character $\varepsilon= \omega^{-s_\varepsilon} \times \omega^{a+s_\varepsilon}$ of $\Delta^2$ re                                                                                                                                                                                    |
| P:ghost compatible with theta AL and p-stabilization_part2 | 4.36           | Formalize        | proposition | Fix $k_0 \geq 2$ and a character $\varepsilon= \omega^{-s_\varepsilon} \times \omega^{a+s_\varepsilon}$ of $\Delta^2$ re                                                                                                                                                                                    |
| P:ghost compatible with theta AL and p-stabilization_part3 | 4.37           | Formalize        | proposition | Fix $k_0 \geq 2$ and a character $\varepsilon= \omega^{-s_\varepsilon} \times \omega^{a+s_\varepsilon}$ of $\Delta^2$ re                                                                                                                                                                                    |
| P:ghost compatible with theta AL and p-stabilization_part4 | 4.38           | Formalize        | proposition | Fix $k_0 \geq 2$ and a character $\varepsilon= \omega^{-s_\varepsilon} \times \omega^{a+s_\varepsilon}$ of $\Delta^2$ re                                                                                                                                                                                    |
| UNLABELED:Notation_4.63_Dig_and_sum_vp                     | 4.63           | Formalize        |             | Introduce Dig(m)=sum of base-p digits; prove/record Eq (E:sum of consecutive valuations): Σ_{m1<i≤m2} v_p(i)=((m2-Dig m2)-(m1-Dig m1))/(p-1). Add a fresh LaTeX label in refactor and a Lean definition+lemma.                                                                                              |
| P:gouvea k-1/p+1 conjecture                                | 4.64           | Formalize        | proposition | Fix a relevant character $\varepsilon$ of $\Delta^2$, and let $k_0 \equiv k_\varepsilon \bmod{(p-1)}$ be a weight.                                                                                                                                                                                          |

---

## Section 5 expansion (“Formalize everything in section 5”)

Interpretation for Lean: **formalize every numbered formal statement** (Definition / Notation / Lemma / Proposition / Theorem / Corollary / Example). Labeled “para” blocks are mostly narrative; I keep them mapped here but mark them *Do Not Formalize* unless they introduce definitional content.

### Table B — All numbered items in Section 5 (Vertices of the Newton polygon of ghost series)

| Label                                                                  | Current Number | Action           | Located Env | Locator Quote/Definition                                                                                                                                                                                |
| ---------------------------------------------------------------------- | -------------- | ---------------- | ----------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| P:para_149                                                             | 5.1            | Do Not Formalize | para        | In this section, we investigate further properties of ghost series.                                                                                                                                     |
| P:para_150                                                             | 5.2            | Do Not Formalize | para        | \emph{We fix $\varepsilon = \omega^{-s_\varepsilon} \otimes \omega^{a+s_\varepsilon}$ a relevant character of $\Delta^2$                                                                                |
| P:para_151                                                             | 5.3            | Do Not Formalize | para        | \emph{Let $G(w,t) = G^{(\varepsilon)}(w,t) = \sum_{n\geq 0} g_n(w) t^n \in \ZZ_p[w]\llbracket t\rrbracket$ denote the co                                                                                |
| P:para_152                                                             | 5.4            | Do Not Formalize | para        | We prove the following two results in this section: \item For $n \in \ZZ_{\geq 0}$ and $w_\star \in \gothm_{\CC_p}$, the                                                                                |
| P:para_153                                                             | 5.5            | Do Not Formalize | para        | Before diving into the more detailed discussion, let us first explain one of the serious subtleties we face in this sect                                                                                |
| N:Delta kell                                                           | 5.6            | Formalize        | notation    | Fix integers $k = k_\varepsilon + (p-1)k_\bullet$ and $\ell$.                                                                                                                                           |
| P:para_154                                                             | 5.7            | Do Not Formalize | para        | We start with several technical lemmas giving estimates of $\Delta'*{k, \ell}$ and $\Delta*{k,\ell}$.                                                                                                   |
| L:estimate Delta kell                                                  | 5.8            | Formalize        | lemma       | For integers $k=k_\varepsilon + (p-1)k_\bullet \geq 2$ and $\ell >0$, we have $$ \Delta_{k,\ell} \geq \frac \ell 2 + \frac{p-1}2 \big \lfloor \frac{\ell - (p+1)k_\bullet}{p^2-1}\big\rfloor.           |
| P:para_155                                                             | 5.9            | Do Not Formalize | para        | The following corollary in fact slightly strengthens the previous lemma.                                                                                                                                |
| C:finer inequality for Delta                                           | 5.10           | Formalize        | corollary   | For integers $k=k_\varepsilon + (p-1)k_\bullet \geq 2$ and $\ell >0$, we have $$ \Delta_{k,\ell} \geq \frac \ell 2 + \frac{p-1}2 \big \lfloor \frac{\ell - (p+1)k_\bullet +p}{p^2-1}\big\rfloor.        |
| L:elementary Digits lemma                                              | 5.11           | Formalize        | lemma       | Let $n$ be a positive integer.                                                                                                                                                                          |
| P:para_156                                                             | 5.12           | Do Not Formalize | para        | In our forthcoming paper where we prove the local ghost conjecture, we need to establish similar bounds for $\Delta_{k,                                                                                 |
| L:upper bound of difference of Delta kell                              | 5.13           | Formalize        | lemma       | Fix integers $k=k_\varepsilon+(p-1)k_\bullet \ge 2$ and $\ell>0$.                                                                                                                                       |
| L:failure of convexity of Delta'                                       | 5.14           | Formalize        | lemma       | For any $k_\bullet \geq 1$, we have $$ \Delta'*{k, (p+1)k*\bullet} - 2\Delta'*{k, (p+1)k*\bullet-1} + \Delta'*{k, (p+1)k*\bullet-2} = -1.                                                               |
| N:linear shift down                                                    | 5.15           | Formalize        | notation    | For integer $k \equiv k_\varepsilon \bmod{(p-1)}$, define $$ \Delta_{k,\ell}^{\prime\prime}=\Delta_{k,\ell}^{\prime} - \lfloor \frac{\ell}{p+1}\rfloor.                                                 |
| L:Delta - Delta' bound                                                 | 5.16           | Formalize        | lemma       | For integers $k \equiv k_\varepsilon \bmod{(p-1)}$ and $\ell >0$, we have $$ 0\le \Delta_{k,\ell} -\Delta'_{k,\ell} \le \frac{p-1}2\lceil \frac{\ell}{p+1}\rceil.                                       |
| P:para_157                                                             | 5.17           | Do Not Formalize | para        | As a consequence of the above estimate, Lemma~\ref{L:estimate Delta kell} and Corollary~\ref{C:finer inequality for Delt                                                                                |
| C:Delta - Delta'                                                       | 5.18           | Formalize        | corollary   | For integers $k \equiv k_\varepsilon \bmod{(p-1)}$ and $\ell >0$, we have $$ \Delta_{k,\ell}^{\prime\prime}\le \Delta_{k,\ell} \le \Delta_{k,\ell}^{\prime} + \frac{p-1}2\lceil \frac{\ell}{p+1}\rceil. |
| P:para_158                                                             | 5.19           | Do Not Formalize | para        | The following slight generalization of Corollary~\ref{C:Delta - Delta'} is tailored for our need in the sequel of this s                                                                                |
| C:Delta - Delta' multi                                                 | 5.20           | Formalize        | corollary   | Fix integers $k_i \equiv k_\varepsilon \bmod{(p-1)}$ and $\ell_i>0$ for $i=1,2$.                                                                                                                        |
| D:near-Steinberg                                                       | 5.21           | Formalize        | definition  | Fix $w_\star \in \gothm_{\CC_p}$, an integer $k \geq 2$ with $k \equiv k_\varepsilon \bmod{(p-1)}$, and an integer $n\ge0$.                                                                             |
| R:near-Steinberg explained                                             | 5.22           | Do Not Formalize | remark      | Let us illustrate the meaning of the notion near-Steinberg in a more intuitive way: by Proposition~\ref{P:ghost compatible with theta AL and                                                            |
| L:near-Steinberg range as an interval                                  | 5.23           | Formalize        | lemma       | Fix $w_\star\in \gothm_{\CC_p}$ and $k=k_\varepsilon+(p-1)k_\bullet\ge2$.                                                                                                                               |
| R:intuition of near-Steinberg                                          | 5.24           | Do Not Formalize | remark      | We provide additional visualization on near-Steinberg ranges by trying to answer the question in vague terms: for each fixed $n$ (and a fixe                                                            |
| Ex:non-vertex picture                                                  | 5.25           | Formalize        | example     | Take $p=5$ and $a=1$.                                                                                                                                                                                   |
| P:para_159                                                             | 5.26           | Do Not Formalize | para        | Before proceeding, we give a general tool to relate the Newton polygon of ghost series at one point $w_\star$ with that                                                                                 |
| P:shifting points wstar to wk_part1                                    | 5.27           | Formalize        | proposition | Let $ \nS_{w_\star, k} = \big(\tfrac 12 d_{k}^\Iw - L_{w_\star, k},, \tfrac 12 d_{k}^\Iw+ L_{ w_\star, k} \big)$ be a n                                                                                 |
| P:shifting points wstar to wk_part2                                    | 5.28           | Formalize        | proposition | Let $ \nS_{w_\star, k} = \big(\tfrac 12 d_{k}^\Iw - L_{w_\star, k},, \tfrac 12 d_{k}^\Iw+ L_{ w_\star, k} \big)$ be a n                                                                                 |
| P:shifting points wstar to wk_part3                                    | 5.29           | Formalize        | proposition | Let $ \nS_{w_\star, k} = \big(\tfrac 12 d_{k}^\Iw - L_{w_\star, k},, \tfrac 12 d_{k}^\Iw+ L_{ w_\star, k} \big)$ be a n                                                                                 |
| P:shifting points wstar to wk_part4                                    | 5.30           | Formalize        | proposition | Let $ \nS_{w_\star, k} = \big(\tfrac 12 d_{k}^Iw - L_{w_\star, k},, \tfrac 12 d_{k}^Iw+ L_{ w_\star, k} \big)$ be a n                                                                                   |
| L:double integral when shifting                                        | 5.31           | Formalize        | lemma       | Let $k=k_\varepsilon + (p-1)k_\bullet\ge2$ and $w_\star\in\gothm_{\CC_p}$.                                                                                                                              |
| P:para_160                                                             | 5.32           | Do Not Formalize | para        | The following immediate corollary of Propositions~\ref{P:shifting points wstar to wk_part1}--\ref{P:shifting points wsta                                                                                |
| C:near-Steinberg => straightline_part1                                 | 5.33           | Formalize        | corollary   | Let $ \nS_{w_\star, k} = \big(\tfrac 12 d_{k}^\Iw - L_{w_\star, k},, \tfrac 12 d_{k}^\Iw+ L_{ w_\star, k} \big)$ be a n                                                                                 |
| C:near-Steinberg => straightline_part2                                 | 5.34           | Formalize        | corollary   | Let $ \nS_{w_\star, k} = \big(\tfrac 12 d_{k}^\Iw - L_{w_\star, k},, \tfrac 12 d_{k}^\Iw+ L_{ w_\star, k} \big)$ be a n                                                                                 |
| P:para_161                                                             | 5.35           | Do Not Formalize | para        | The following theorem, which describes the shapes of $\NP(G(w_\star, -))$, is the main result of this paper.                                                                                            |
| T:near Steinberg = non-vertex_part1                                    | 5.36           | Formalize        | theorem     | Fix $n\ge0$ and $w_\star\in\gothm_{\CC_p}$.                                                                                                                                                             |
| T:near Steinberg = non-vertex_part2                                    | 5.37           | Formalize        | theorem     | Fix $n\ge0$ and $w_\star\in\gothm_{\CC_p}$.                                                                                                                                                             |
| T:near Steinberg = non-vertex_part3                                    | 5.38           | Formalize        | theorem     | Fix $n\ge0$ and $w_\star\in\gothm_{\CC_p}$.                                                                                                                                                             |
| C:integral slopes of ghost series_part1                                | 5.39           | Formalize        | corollary   | Fix $w_\star\in\gothm_{\CC_p}$.                                                                                                                                                                         |
| P:para_162                                                             | 5.40           | Do Not Formalize | para        | Before proving the theorem, we first prove the following technical lemma on the comparison of sizes of two near-Steinber                                                                                |
| L:comparison of two near-Steinberg ranges with a nonempty intersection | 5.41           | Formalize        | lemma       | Suppose that two positive integers $k_i = k_\varepsilon + (p-1)k_{i\bullet}$ for $i=1,2$ satisfy the condition that the                                                                                 |
| P:para_163                                                             | 5.42           | Do Not Formalize | para        | Now we are ready to prove Theorems~\ref{T:near Steinberg = non-vertex_part1}--\ref{T:near Steinberg = non-vertex_part3}.                                                                                |
| Notation:L+ and L-                                                     | 5.43           | Formalize        | notation    | Define $L_+ = L_+(w_\star, k)$ and $L_- = L_-(w_\star, k)$ by $$ L_\pm = \lfloor \frac 12 \Delta_{k, \ell_\pm}\rfloor, \qquad \ell_\pm = \pm \lceil \frac{2v_p(w_\star-w_k)}{p-1}\rceil.                |
| C:integral slopes of ghost series_part2                                | 5.44           | Formalize        | corollary   | Fix $w_\star\in \gothm_{\CC_p}$.                                                                                                                                                                        |
| Ex:failure of integral slopes for Cwstar                               | 5.45           | Formalize        | example     | Let $p=5$ and $a=1$.                                                                                                                                                                                    |
| P:para_164                                                             | 5.46           | Do Not Formalize | para        | This proposition above implies the following, which is in close relation with Breuil--Buzzard--Emerton's Conjecture~\ref                                                                                |
| P:vertices of Deltak_part1                                             | 5.50           | Formalize        | proposition | Fix an integer $k = k_\varepsilon + (p-1)k_\bullet\ge2$.                                                                                                                                                |
| P:vertices of Deltak_part2                                             | 5.51           | Formalize        | proposition | Fix an integer $k=k_\varepsilon+(p-1)k_\bullet \ge2$.                                                                                                                                                   |
| C:vertices of Newton polygon at wk                                     | 5.52           | Formalize        | corollary   | Fix an integer $k=k_\varepsilon+(p-1)k_\bullet \ge2$.                                                                                                                                                   |
| C:boundary of Steinberg ranges are vertices                            | 5.53           | Formalize        | corollary   | Fix $w_\star\in\gothm_{\CC_p}$.                                                                                                                                                                         |
| Ex:pathological Steinberg range                                        | 5.49           | Formalize        | example     | We give a example of a situation where near-Steinberg ranges are nested.                                                                                                                                |
| R:boundary of Delta is okay                                            |                | Do Not Formalize | remark      | (This remark is labeled but does not appear as a numbered `\newlabel` in `paper.aux`; treat as narrative.)                                                                                              |

---

## Dependency notes (what gets dropped vs. what stays)

### Drop (geometry/representation setup)

* Anything whose *meaning* depends on (\widetilde{\rmH}), (\bar\rho), explicit (\GL_2(\mathbb F_p)) decomposition, completed cohomology, etc.
* The derivation inside (\S4.10) (explicit computation of (\rmS_k^\unr)) and equation (4.11.1) per instruction.

### Keep (pure combinatorics / (p)-adic / convex-geometry)

* Newton polygon definition (generalized), slopes/vertices logic.
* Digit-sum and (v_p)-sum identities (Notation 4.63).
* All ghost-series combinatorics: multiplicities, degree increments, “remove a factor at (w_k)”, compatibility propositions 4.34/4.36–4.38.
* Entire Section 5 formal statements: bounds for (\Delta_{k,\ell}), near-Steinberg ranges, vertex criteria, integrality of slopes.

---

If you want, the next step (still **not** writing the full LaTeX) is: I can turn this into a **Lean-oriented module graph** (files + namespaces) showing where each “Redefine” becomes a `def` and which propositions become `theorem`s that unfold those defs.
