# Ghosts and displaced-parity classification in dimensions 4–7

**Author:** Yaoling Yang

## Result and definitions

Let $V_d$ be the complex scheme of trace-one rank-one idempotents described by Khodaiemehr, [Definition II.1 and equation (1)](https://arxiv.org/abs/2611.01524). Write

$$
 \Pi=ab^T/S,\qquad S=b^Ta\ne0,
$$

and impose, for every nonzero Weyl label $p$,

$$
 (d+1)\operatorname{tr}(\Pi D_p)\operatorname{tr}(\Pi D_{-p})=1.
$$

Hermitian points form $S_d$. Let $R e_j=e_{-j}$, and for an actual matrix $u=D_qR$ define

$$
 \Gamma_u=\{\Pi\in V_d:\Pi^\dagger=u\Pi u^{-1}\},\qquad
 G_d=\bigcup_{u\in\mathcal P_d}\Gamma_u,
$$

where $\mathcal P_d$ is the set of distinct displaced-parity matrices. Khodaiemehr's ghost set is $G_d\setminus S_d$. We prove $S_d\cap G_d=\varnothing$, so this equals $G_d$ in the dimensions below.

The inherited exact classifications give:

| $d$ | All points $\lvert V_d\rvert$ | Hermitian $\lvert S_d\rvert$ | Non-Hermitian | Ghosts $\lvert G_d\rvert$ | $\lvert\Gamma_R\rvert$ |
|---:|---:|---:|---:|---:|---:|
| 4 | 512 | 256 | 256 | 256 | 64 |
| 5 | 4,000 | 2,000 | 2,000 | 2,000 | 80 |
| 6 | 6,912 | 3,456 | 3,456 | 3,456 | 384 |
| 7 | 32,928 | 16,464 | 16,464 | 16,464 | 336 |

Thus $V_d=S_d\sqcup G_d$ and $|S_d|=|G_d|$ for $4\le d\le7$. This proves the corresponding finite-dimensional cases of Conjecture III.1. Khodaiemehr already verified numerically that every non-Hermitian point in dimensions 4 and 5 is a displaced-parity ghost ([Table II](https://arxiv.org/abs/2611.01524)). The total point counts, reducedness, and orbit completeness used here are exact computer-assisted results. Their computational prerequisites passed the clean replay recorded in [replay/VALIDATION.md](../replay/VALIDATION.md). The parity lemmas, nonintersection proof, and ghost coverage argument below are written mathematical arguments.

## 1. Actual parity matrices, including even-dimensional signs

Use the ACFW phase convention [ACFW, §2](https://arxiv.org/abs/1703.05981):

$$
 \tau=-e^{\pi i/d},\quad \omega=\tau^2,\quad
 D_{a,b}=\tau^{ab}X^aZ^b.
$$

Labels in operator identities are integer labels until the final matrix is reduced. The parity matrices obey

$$
 D_p^\dagger=D_{-p},\qquad RD_pR=D_{-p},\qquad
 u_q=D_qR=u_q^\dagger,\qquad u_q^2=I.
$$

For odd $d$, labels modulo $d$ give exactly $d^2$ distinct actual matrices $u_q$, all of trace 1. For even $d$, shifting a label by $d\alpha$, $\alpha\in\mathbb Z^2$, gives

$$
 D_{q+d\alpha}=(-1)^{\alpha_1q_2+\alpha_2q_1}D_q.
$$

If both coordinates of $q\bmod d$ are even, all four lifts modulo $2d$ give the same matrix. Otherwise, the lifts give both $u_q$ and $-u_q$, each twice. Therefore the number of distinct actual matrices is

$$
 |\mathcal P_d|=\frac{d^2}{4}+2\frac{3d^2}{4}=\frac{7d^2}{4}.
$$

A direct diagonal calculation gives

$$
 \operatorname{tr}(D_qR)=
 \begin{cases}
 1,&d\text{ odd},\\
 2,&d\text{ even and }q_1,q_2\text{ are even},\\
 0,&d\text{ even and at least one coordinate of }q\text{ is odd}.
 \end{cases}
$$

The trace determines the eigenspace dimensions of each involution. In even dimensions, the trace-2 cases have dimensions $((d+2)/2,(d-2)/2)$. Trace-zero cases have $(d/2,d/2)$. In odd dimensions, the dimensions are $((d+1)/2,(d-1)/2)$.

| $d$ | Distinct actual matrices | Trace / eigenspace dimensions | Number of matrices |
|---:|---:|---|---:|
| 4 | 28 | trace 2, $(3,1)$ | 4 |
| 4 |  | trace 0, $(2,2)$ | 24 |
| 5 | 25 | trace 1, $(3,2)$ | 25 |
| 6 | 63 | trace 2, $(4,2)$ | 9 |
| 6 |  | trace 0, $(3,3)$ | 54 |
| 7 | 49 | trace 1, $(4,3)$ | 49 |

The number of actual matrices differs from the number of distinct conjugation actions in even dimensions: $u$ and $-u$ induce the same action. We count actual matrices here, as the branch table does.

### Trace-zero parity branches are empty

Suppose $d$ is even and $\Pi\in\Gamma_{u_q}$. The displacements $D_{(d/2,0)}=X^{d/2}$ and $D_{(0,d/2)}$ are Hermitian involutions. Put $a_p=\operatorname{tr}(\Pi D_p)$ for either label. Since $-p=p$ as an actual Hermitian displacement, the SIC equation gives

$$
 a_p^2=\frac1{d+1},
$$

so $a_p$ is real and nonzero. The ghost relation and cyclicity of trace imply

$$
 \overline{a_{(d/2,0)}}=(-1)^{q_2}a_{(d/2,0)},\qquad
 \overline{a_{(0,d/2)}}=(-1)^{q_1}a_{(0,d/2)}.
$$

Consequently both $q_1$ and $q_2$ must be even. Thus every trace-zero parity branch in dimensions 4 and 6 is empty, and every potentially nonempty branch has an even center.

## 2. Clifford, transpose, and Galois transport

### Clifford and factor swap

Khodaiemehr's [Lemma IV.1](https://arxiv.org/abs/2611.01524) proves preservation of the SIC and ghost loci under Clifford and antiunitary transport. We record the Clifford formula and the algebraic transpose action used in this repository, including the even-dimensional signs.

If $U$ is a Clifford unitary, then

$$
 \Pi\in\Gamma_u\quad\Longrightarrow\quad
 U\Pi U^{-1}\in\Gamma_{UuU^{-1}}.
$$

The symplectic action of $R$ is $-I$, central in the symplectic group. Hence $UuU^{-1}$ is a scalar times a displaced parity. Both matrices are Hermitian involutions, so that scalar is $\pm1$. The trace-one odd-dimensional case forces the plus sign. The even trace-two case also forces plus. In the trace-zero case both signs occur in $\mathcal P_d$. Therefore the actual parity family is closed under Clifford conjugation.

Let $T(\Pi)=\Pi^T$, which swaps the two projective factors. It is an algebraic action on the complexified scheme. Direct transposition gives

$$
 \Pi\in\Gamma_u\quad\Longrightarrow\quad
 \Pi^T\in\Gamma_{u^{-T}},\qquad
 u_{a,b}^{-T}=\overline{u_{a,b}}=u_{a,-b}.
$$

Thus $G_d$ is stable under $E_d=\langle C_d,T\rangle$, where $C_d$ is the ordinary projective Clifford group. On Hermitian points this agrees with the usual antiunitary extension. On non-Hermitian points the action meant here is factor swap. It must not be silently reinterpreted as physical antiunitary conjugation.

The displacement center moves by

$$
 D_vu_qD_v^{-1}=u_{q+2v}.
$$

This formula will also give transitivity on the allowed centers.

### Galois images require the actual conjugation

Work in a finite Galois closure containing the point coordinates, the cyclotomic entries of the displacement operators, and their images, so all automorphisms below act on one field. Let $c$ be the specified complex conjugation and let $g$ be a field automorphism. Their restrictions commute on the cyclotomic subfield, whose Galois group is abelian. For $Q=g(\Pi)$, applying $g$ first gives

$$
 c_g(Q)^T=g(u)Qg(u)^{-1},\qquad c_g=gcg^{-1}.
$$

In general $c_g$ differs from the actual conjugation $c$. Set

$$
 \delta_g=cgcg^{-1}.
$$

Applying the automorphisms to the parity relation $\Pi^\dagger=u\Pi u^{-1}$ gives

$$
 Q^\dagger=g(u)\,\delta_g(Q)\,g(u)^{-1}.
$$

If $g(\tau)=\tau^k$, the exact signed-label action on the parity is

$$
 g(u_{a,b})=u_{a,kb}.
$$

In this case $g(u)$ is the displaced-parity operator for the image center. The identity shows that $Q$ belongs to the displayed branch $\Gamma_{g(u)}$ for the chosen embedding if and only if $\delta_g(Q)=Q$. In particular, a Galois image is not automatically a ghost: the pointwise condition on its actual conjugation must be proved.

## 3. Hermitian points and ghosts do not intersect

This argument uses no classification count. First move the center of a putative ghost to zero using the displacement formula. For odd $d$, multiplication by 2 is invertible modulo $d$. For even $d$, the previous section shows that a nonempty branch has an even center, which is also in the image of multiplication by 2. It is enough to rule out a point in $\Gamma_R\cap S_d$.

If $\Pi$ is a Hermitian rank-one projector in $\Gamma_R$, it commutes with $R$. Its image is an eigenspace line for $R$, so

$$
 \operatorname{tr}(\Pi R)=\epsilon,\qquad \epsilon\in\{1,-1\}.
$$

For $p\ne0$, write $a_p=\operatorname{tr}(\Pi D_p)$. Hermiticity, commutation with $R$, and the SIC equations give

$$
 a_{-p}=a_p=\overline{a_p},\qquad
 a_p=\frac{\delta_p}{\sqrt{d+1}},\quad \delta_p\in\{1,-1\}.
$$

Let $t=1$ for odd $d$, $t=2$ for even $d$, and let $L=(\mathbb Z/d\mathbb Z)^2$ in odd dimension and $L=2(\mathbb Z/d\mathbb Z)^2$ in even dimension. Weyl-basis orthogonality gives

$$
 R=\frac{t}{d}\sum_{p\in L}D_p.
$$

Taking the trace against $\Pi$ yields, for an integer $K$,

$$
 d\epsilon=t+\frac{tK}{\sqrt{d+1}}.
$$

For $d\ge4$, $d\epsilon-t\ne0$. The equality would force $\sqrt{d+1}$ to be rational. For $d=4,5,6,7$, $d+1=5,6,7,8$ is not a square. Therefore

$$
 \boxed{S_d\cap G_d=\varnothing\quad(4\le d\le7).}
$$

This argument is limited to the stated dimensions. It does not settle dimensions where $d+1$ is a square.

## 4. Dimensions 4–6: one existing ghost covers the non-Hermitian part

The inherited exact orbit classifications give one non-Hermitian $E_d$-orbit in each of dimensions 4, 5, and 6:

| $d$ | Non-Hermitian ordinary Clifford orbits | Non-Hermitian $E_d$-orbits | Size |
|---:|---|---:|---:|
| 4 | one orbit | one | 256 |
| 5 | two orbits, exchanged by $T$ | one | 2,000 |
| 6 | two orbits, exchanged by $T$ | one | 3,456 |

An unconditional existence theorem supplies one standard rank-one, trace-one ghost fiducial that is $R$-Hermitian: $\widetilde\Pi^\dagger=R\widetilde\Pi R$. This is the $r=1$ case of Appleby–Flammia–Kopp, [arXiv:2609.39192, Theorem 1.3](https://arxiv.org/abs/2609.39192). Its clause (4) is exactly the parity-Hermitian relation used here. Their operator $U_P$ is $R$, and their displacement phase $e^{(d+1)\pi i p_1p_2/d}$ equals $\tau^{p_1p_2}$ in the ACFW convention. For this specialization the hypotheses reduce to $1<(d-1)/2$ and $(d^2-1)/(d-1)=d+1\in\mathbb Z$, which hold for each $d\ge4$ considered here. This existence input assumes no Stark or Galois-switching conjecture.

Khodaiemehr's [Theorem II.4](https://arxiv.org/abs/2611.01524) already places this ghost in $\Gamma_{U_P}\subset V_d$. The rank-one identity explains the conversion: for a trace-one projector, $\Pi A\Pi=\operatorname{tr}(\Pi A)\Pi$. Applying it to displacement operators converts the construction's equal-overlap conditions into the defining products for $V_d$, so $\widetilde\Pi\in\Gamma_R$. The nonintersection result shows it is non-Hermitian. It therefore lies in the unique non-Hermitian extended orbit in each of dimensions 4–6. Since $G_d$ is $E_d$-stable, that whole orbit consists of ghosts. Hence every non-Hermitian point is a ghost in these dimensions.

This step depends on the *complete* inherited orbit classifications, not merely on the existence of a known non-Hermitian orbit. The inherited evidence includes the full characteristic-zero orbit counts and reducedness, based on exact arithmetic and the corresponding proof records in `sources/d4-upper/`, `sources/exact-d4-d5/`, and `sources/d6/`.

## 5. Dimension 7: exact parity-Hermitian checks on G1 and G2

The exact orbit audit supplies four field-valued seeds F1, F2, G1, G2. The six ordinary Clifford orbits are represented by F1, $T(F1)$, F2, G1, $T(G1)$, and G2. Each has 5,488 points, and they are pairwise disjoint. F1 and F2 are Hermitian. The three non-Hermitian ordinary orbits are G1, $T(G1)$, and G2. We check G1 and G2 directly in the specified complex embedding, then use Clifford and transpose transport to cover their orbits. The extended families are:

- F1: 10,976 points in two ordinary orbits, with extended stabilizer 3.
- F2: 5,488 points in one ordinary orbit, with extended stabilizer 6.
- G1: 10,976 points in two ordinary orbits, with extended stabilizer 3.
- G2: 5,488 points in one ordinary orbit, with extended stabilizer 6.

Thus G2 has ordinary stabilizer 3, while its transpose lies in the same ordinary orbit and enlarges its extended stabilizer to 6.

The field relations are

$$
 s_0=\sqrt2,\quad r_0>0,\quad r_0^2=s_0-\tfrac12,\quad i^2=-1,
 \quad\Phi_7(\zeta)=0,
$$

$$
 G=\zeta+\zeta^2-\zeta^3+\zeta^4-\zeta^5-\zeta^6,
 \quad G^2=-7,\quad s=-s_0,\quad r=G/(2r_0).
$$

Complex conjugation in this embedding satisfies

$$
 \bar s=s,\qquad\bar r=-r,\qquad\bar i=-i,\qquad\bar\zeta=\zeta^{-1}.
$$

Both seeds have $a=(1,u,u,v,u,v,v)$. Parity $R$ interchanges the positions occupied by $u$ and $v$.

### G1

Set

$$
 \eta=1+i(2s-1),\quad \kappa=-1+s/2,\quad N=16-4s,
$$

$$
 u=(\kappa-r)/\eta,\quad v=(\kappa+r)/\eta,
 \quad c=(10-4s)/N,
$$

$$
 e=\eta(\kappa-r)/N,\qquad f=\eta(\kappa+r)/N,
 \quad b=(c,e,e,f,e,f,f).
$$

The displayed field relations give $c\in\mathbb R\setminus\{0\}$,

$$
 \bar b=cRa,\qquad \bar a=c^{-1}Rb,
$$

and

$$
 \eta\bar\eta+6(\kappa^2+r^2)=N,
 \qquad b^Ta=c+\frac{6(\kappa^2+r^2)}N=1.
$$

Therefore, for $\Pi=ab^T$,

$$
 \Pi^\dagger=\bar b\bar a^T=R ab^T R=R\Pi R.
$$

### G2

Set $t=sr$ and

$$
 u=(-1-s+t)/2,\quad v=(-1-s-t)/2,\quad
 c=(4+6s)^{-1},\quad b=ca.
$$

Here $\bar t=-t$, $c$ is nonzero and real, and $\bar a=Ra$. The relation $t^2=2s-1$ gives

$$
 1+3(u^2+v^2)=4+6s,
 \qquad b^Ta=c\bigl(1+3(u^2+v^2)\bigr)=1.
$$

Thus $\bar b=cRa$, and again $\Pi^\dagger=R\Pi R$. These are exact coordinate identities. No floating-point equality test is involved.

For all four seed pairs, exact arithmetic gives $b^Ta=1$ and $8Z(p)Z(-p)-1=0$ for all 24 representatives, where $Z(p)=b^TD_pa$. It also verifies the 49 identities

$$
 8\sum_{j=0}^{6}a_jb_{j+\alpha}b_{j+\beta}a_{j+\alpha+\beta}
 =\mathbf1_{\alpha=0}+\mathbf1_{\beta=0}
 \qquad(\alpha,\beta\in\mathbb F_7).
$$

The inherited exact report records `Z0_is_one=true`, `q_bad_count=0`, `quartic_bad_count=0`, `fixed_by_P=true`, and the expected Hermitian boolean for each seed. The exact group checks verify Clifford covariance, the Zauner trace, and all four reference-orbit connections. The reductions at 673 and 953 establish separation and stabilizer upper bounds only. In particular, they are not used to assert that G1 or G2 exists in characteristic zero.

It follows that G1 and G2 lie in $\Gamma_R$. Clifford conjugation carries the first to the G1 ordinary orbit. Transpose carries it to $T(G1)$, still in some displaced-parity branch. G2's transpose already lies in its ordinary orbit. Hence all 16,464 non-Hermitian points are ghosts. The nonintersection theorem excludes every Hermitian point from every ghost branch.

## 6. Unique centers and exact branch sizes

First, the Weyl–Heisenberg displacement group acts freely on every point of $V_d$. If $D_p$ with $p\not\equiv0\pmod d$ fixed $\Pi$, then $D_p$ would commute with $\Pi$. The rank-one identity gives

$$
 1=\operatorname{tr}(\Pi^2)
  =\operatorname{tr}(\Pi D_p\Pi D_p^{-1})
  =\operatorname{tr}(\Pi D_p)\operatorname{tr}(\Pi D_p^{-1})
  =\frac1{d+1},
$$

a contradiction.

If a point lay in both $\Gamma_{u_q}$ and $\Gamma_{u_r}$, then $u_r^{-1}u_q$ would fix it projectively. This is a scalar times the displacement with label $q-r$, so freeness forces $q=r\pmod d$. In even dimensions, the only nonempty centers have both coordinates even, and their four lifts modulo $2d$ give the same actual matrix. Thus every ghost belongs to exactly one actual nonempty branch.

For odd $d$, every center is nonempty and the displacement action $q\mapsto q+2v$ is transitive across the $d^2$ centers. Each branch has $|G_d|/d^2$ points. For even $d$, the $d^2/4$ even centers form one transitive family, so each nonempty branch has $4|G_d|/d^2$ points. The resulting actual-matrix counts are:

| $d$ | Nonempty branches | Points per branch | Empty branches | Total ghosts |
|---:|---:|---:|---:|---:|
| 4 | 4 trace-2 matrices | 64 | 24 trace-zero matrices | 256 |
| 5 | 25 trace-1 matrices | 80 | 0 | 2,000 |
| 6 | 9 trace-2 matrices | 384 | 54 trace-zero matrices | 3,456 |
| 7 | 49 trace-1 matrices | 336 | 0 | 16,464 |

Each ghost is assigned to its unique center by the transport rule. No branch count multiplies or divides by a weight denominator, and no point is counted twice.

## 7. Inherited evidence and limits

The exact total point counts and classifications are inherited from:

- `sources/d4-upper/` and `sources/exact-d4-d5/` for the complete d=4 and d=5 point schemes and orbit data.
- `sources/d6/` for the complete d=6 count and ordinary/extended orbit classification.
- `sources/d7/` and `independent/d7-orbits/` for the d=7 exact seed and orbit classification.

The arguments assembled in this note include the actual even-dimensional parity count, the trace-zero branch exclusion, the Clifford/transpose/Galois transport statements, $S_d\cap G_d=\varnothing$, the d=4–6 orbit reduction from an unconditional ghost existence theorem, the direct d=7 G1/G2 conjugation checks, and the unique-center branch counts. The cited transport and existence results are due to Khodaiemehr and Appleby–Flammia–Kopp as identified above. The classifications depend on exact algebraic and modular computations and their stated proof interfaces. The clean replay reran the computational prerequisites. Its returned records are included under `replay/clean-run/`. No proof-assistant formalization is supplied.

For d=4–6, the external existence input is a single proved fiducial, while completeness comes from the inherited one-non-Hermitian-extended-orbit classification. For d=7, completeness comes from the inherited six-orbit lower bound combined with the finite intersection budget giving the matching upper bound. The result does not claim that every non-Hermitian SIC in arbitrary dimension is a displaced-parity ghost, and it does not settle Conjecture III.1 outside $4\le d\le7$.
