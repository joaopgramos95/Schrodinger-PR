# Self-contained mathematics for the three remaining target axioms

This note gives a proof-complete mathematical route for the three target
statements `hom_strichartz`, `zero_extension_jump`, and
`one_step_propagation`.  “Self-contained” here means that every analytic step
not expected from general measure theory, integration, Fourier analysis, and
Banach/Hilbert-space facts in Mathlib is stated and proved below.

There are four convention/interface points which must be fixed in a literal
formalization.

1. The implementation keeps the **lower** normal half-space:
   \(G=\mathbf 1_{\{s<0\}}F\).  Thus the jump signs are
   \[
   (\mathbf 1_{s<0}h)''
   =\mathbf 1_{s<0}h''-h'(0)\delta _0-h(0)\delta'_0.
   \]
   The signs printed in the paper are for the upper half-space.

2. The spatial Fourier transform used in `Carleman2D.lean` has phase
   \(e^{-2\pi i z\cdot\xi}\).  Consequently the correct conjugated symbol is
   \[
   i\partial_t+\beta^2-4\pi^2|\xi|^2-4\pi i\beta\xi_1.
   \]
   The definitions of `TbetaHat` and `TbetaSymbol` have now been corrected to
   include these \(2\pi\)-factors.  Likewise,
   `fourier_section_identification` now assumes the conjugated equation
   \(P_\beta w=f\), rather than the free equation \(Pw=f\).  These corrections
   align the displayed inverse with the Mathlib-normalized Fourier transform;
   the remaining work is the proof of the corrected identification theorem.

3. In the one-step proof, the translated potential used in the global
   one-slab theorem must be multiplied by the time indicator of \((a,b)\).
   Otherwise the hypothesis only controls its norm on \((a,b)\), while the
   conclusion requires a global \(Y\)-norm.

4. The trace calculation starts with compactly supported tests.  The Lean
   statement uses arbitrary Schwartz tests.  A quantitative trace bound plus
   Schwartz cutoffs supplies the missing passage.  Similarly, separated-test
   approximation must preserve the condition that the time support lies in
   the open set \(I\).

The supplied July 2026 mathematical supplement uses the unitary Fourier
phase \(e^{-ix\xi}\), so its symbols intentionally omit the \(2\pi\)-factors
in point 2.  Its Galilean acceleration sign, far-moment factor, and order of
time localization agree with the implementation after translating this
Fourier convention.

Current Lean status for the one-step package: the explicit cutoffs, their
support separation, the moving boundary, the exact acceleration split, and
the scale-uniform estimate
\[
\int |\omega''(t)|\,dt\le
\frac{6}{\delta}\int|\rho''(s)|\,ds
\]
are proved.  The near potential now has the compiled bound
\[
\|A_{\rm near}\|_{L^1_tL^\infty_x}
\le 3\left(\int|\rho''|\right)\frac{h^2}{\delta}.
\]
The old `moment_error` axiom has been replaced by a theorem, including the
linear moment bound
\[
|y_1|e^{\beta y_1}\le(h+1)e^{-\beta h}
\quad(\beta\ge1,\ y_1\le-h).
\]
Spatial translations and the Galilean phase are proved to preserve the
section, mixed, spacetime, and `carlemanXprimeNorm` seminorms by measurable
equivalences.  The remaining Galilean axiom has consequently been narrowed
to the weak distributional equation itself.  The effective-potential
smallness constant required by `one_step_propagation` is also now constructed
in Lean.

## I. Shared analytic lemmas

### I.1. One-dimensional HLS in exactly the needed range

For \(0<\alpha<1\), define
\[
I_\alpha f(t)=\int_{\mathbb R}|t-s|^{-\alpha}|f(s)|\,ds.
\]
If \(1<p<q<\infty\) and
\[
\frac1q=\frac1p-(1-\alpha),
\]
then
\[
\|I_\alpha f\|_q\le C_{p,\alpha}\|f\|_p.
\]

Proof.  Let \(Mf\) be the centered Hardy--Littlewood maximal function.
The one-dimensional greedy interval selection gives
\[
|\{Mf>\lambda\}|\le \frac{3}{\lambda}\|f\|_1.
\]
Indeed, cover a compact subset of the superlevel set by intervals whose
averages exceed \(\lambda\), choose a disjoint greedy subfamily, and note that
the triples of the chosen intervals cover the compact set.  Inner regularity
removes compactness.

Apply this weak estimate to
\(f\mathbf 1_{\{|f|>\lambda/2\}}\).  Since the maximal function of the
remaining part is at most \(\lambda/2\),
\[
|\{Mf>\lambda\}|\le
\frac6\lambda\int_{|f|>\lambda/2}|f|.
\]
The layer-cake identity and Tonelli give, for \(p>1\),
\[
\begin{aligned}
\|Mf\|_p^p
&=p\int_0^\infty \lambda^{p-1}|\{Mf>\lambda\}|\,d\lambda\\
&\le \frac{6p\,2^{p-1}}{p-1}\|f\|_p^p.
\end{aligned}
\]

For \(R>0\), dyadic shells give
\[
\int_{|t-s|<R}|t-s|^{-\alpha}|f(s)|\,ds
\le C_\alpha R^{1-\alpha}Mf(t).
\]
Hölder on the complement gives
\[
\int_{|t-s|\ge R}|t-s|^{-\alpha}|f(s)|\,ds
\le C_{p,\alpha}R^{1-\alpha-1/p}\|f\|_p.
\]
Set \(R=(\|f\|_p/Mf(t))^p\), with the zero cases handled separately.  If
\(\theta=p/q=1-p(1-\alpha)\), this yields
\[
I_\alpha f(t)
\le C(Mf(t))^{p/q}\|f\|_p^{1-p/q}.
\]
Raising to the \(q\)-th power, integrating, and using the strong maximal
bound proves HLS.

The application below is
\[
p=q',\qquad \alpha=\frac2q,
\]
for which
\(1/q=1/q'-(1-2/q)\).

### I.2. The compatible Riesz--Thorin estimate

Suppose an operator is defined on simple functions and has compatible
extensions
\[
T:L^1\to L^\infty,\quad \|T\|\le M_0,
\qquad
T:L^2\to L^2,\quad \|T\|\le M_1.
\]
For \(2\le r\le\infty\), put \(\vartheta=2/r\).  Then
\[
\|Tf\|_r
\le M_0^{1-\vartheta}M_1^\vartheta\|f\|_{r'}.
\]

For bounded simple \(f,g\) supported on finite-measure sets, normalize
\(\|f\|_{r'}=\|g\|_{r'}=1\), and write
\(u=f/|f|\), \(v=g/|g|\), with value zero at zeros.  For
\(0\le\operatorname{Re}z\le1\), set
\[
f_z=u|f|^{r'((1-z)+z/2)},
\qquad
g_z=v|g|^{r'((1-z)+z/2)}.
\]
Because \(\vartheta=2/r\), one has
\(r'(1-\vartheta/2)=1\), so
\(f_\vartheta=f\) and \(g_\vartheta=g\).  On the left boundary,
\[
\|f_{iy}\|_1=\|g_{iy}\|_1=1,
\]
and on the right boundary,
\[
\|f_{1+iy}\|_2=\|g_{1+iy}\|_2=1.
\]
The scalar function \(z\mapsto\int (Tf_z)g_z\) is analytic in the strip and
continuous on its closure.  The two operator estimates bound its boundary
values by \(M_0\) and \(M_1\).  Hadamard three-lines at
\(\operatorname{Re}z=\vartheta\) gives
\(|\int(Tf)g|\le M_0^{1-\vartheta}M_1^\vartheta\).  Taking the supremum over
\(g\), then using truncation to remove zeros and unbounded values and density
to remove the simple-function restriction, proves the estimate.  This
argument proves compatibility as well as the norm bound; no identification
of two independently constructed operators is assumed.

### I.3. Mixed-norm norming and completeness

For \(1<q,r<\infty\), a jointly measurable \(H\) with finite
\(L^q_tL^r_x\)-norm is normed by \(L^{q'}_tL^{r'}_x\).  If
\(m(t)=\|H(t)\|_r\) and \(N=\|m\|_q>0\), define
\[
g_t(x)=
\begin{cases}
\overline{H(t,x)}|H(t,x)|^{r-2}/m(t)^{r-1},&m(t)>0,\\
0,&m(t)=0,
\end{cases}
\]
and
\[
G(t,x)=\frac{m(t)^{q-1}}{N^{q-1}}g_t(x).
\]
Then \(\|G\|_{L^{q'}L^{r'}}=1\) and \(\int HG=N\).  This gives the exact
duality formula directly from measurability and scalar integration.

At \(r=\infty\), choose a countable dense subset \((g_n)\) of the closed unit
ball of \(L^1_x\).  For every \(h\in L^\infty\),
\[
\|h\|_\infty=\sup_n\left|\int h g_n\right|.
\]
For jointly measurable \(H\), the functions
\(a_n(t)=\int H(t,x)g_n(x)\,dx\) are measurable.  Given
\(0<\varepsilon<1\), choose measurably the least \(n(t)\) such that
\[
|a_{n(t)}(t)|\ge(1-\varepsilon)m(t),
\qquad m(t)=\|H(t)\|_\infty.
\]
Multiply \(g_{n(t)}\) by the phase
\(\overline{a_{n(t)}}/|a_{n(t)}|\), and by the outer norming factor
\(m^{q-1}/\|m\|_q^{q-1}\).  The resulting \(G\) has
\(L^{q'}_tL^1_x\)-norm at most one and pairs with \(H\) to at least
\((1-\varepsilon)\|H\|_{L^qL^\infty}\).  Letting
\(\varepsilon\downarrow0\) proves endpoint norming.

Finite sums \(\sum_j\eta_j(t)\phi_j(x)\), with both factors smooth and
compactly supported, are dense in every \(L^{q'}_tL^{r'}_x\) used here,
including \(r'=1\).  To see this, first approximate by Bochner simple
functions; approximate their spatial coefficients by compactly supported
smooth functions and their finite-measure time indicators by smooth compactly
supported functions.  The tensor norm factorizes, so the two errors are
controlled separately.

Completeness can be proved without a nonseparable Bochner-space theorem.  From
a Cauchy sequence \((H_n)\), take a subsequence with
\[
\|H_{n_{k+1}}-H_{n_k}\|_{L^qL^r}\le2^{-k}.
\]
Let \(d_k(t)=\|H_{n_{k+1}}(t)-H_{n_k}(t)\|_r\).  Minkowski gives
\(\sum_kd_k(t)<\infty\) for almost every \(t\).  For such \(t\), Tonelli
(or the essential-supremum bound when \(r=\infty\)) shows that the pointwise
telescoping series is absolutely convergent for almost every \(x\).  Its
pointwise limit is jointly measurable and the tail is bounded in mixed norm
by \(\|\sum_{k\ge K}d_k\|_q\).  The original Cauchy sequence therefore
converges to the same limit.

## II. Homogeneous Strichartz

### II.1. The free kernel

With the Mathlib Fourier convention, the free multiplier is
\[
e^{-4\pi^2it\xi^2}.
\]
For \(t\ne0\) and Schwartz \(f\),
\[
S(t)f(x)=\frac1{\sqrt{4\pi it}}
\int_{\mathbb R}e^{i(x-y)^2/(4t)}f(y)\,dy.
\]
To justify the formula, insert \(e^{-\epsilon\xi^2}\).  The complex Gaussian
identity with \(z=\epsilon+4\pi^2it\) gives the regularized kernel
\[
K_{\epsilon,t}(u)=rac{\sqrt\pi}{\sqrt z}
e^{-\pi^2u^2/z}.
\]
On the frequency side dominated convergence uses \(\widehat f\in L^1\).  On
the physical side, for \(0<\epsilon\le1\), the exponential has modulus at
most one and the prefactor is uniformly bounded because \(t\ne0\); dominated
convergence uses \(f\in L^1\).  The limit is the displayed kernel, with the
principal square root.  In particular,
\[
\|S(t)f\|_\infty
\le(4\pi|t|)^{-1/2}\|f\|_1.
\]

Unitarity on \(L^2\) and Section I.2 imply, for \(2\le r\le\infty\),
\[
\|S(t)g\|_r
\le C_r|t|^{-\alpha}\|g\|_{r'},
\qquad
\alpha=\frac12-\frac1r.
\]

### II.2. The TT-star and adjoint estimates

Let \((q,r)\ne(\infty,2)\) be admissible.  Then \(q<\infty\),
\(2<r\le\infty\), and
\[
\alpha=\frac12-\frac1r=\frac2q.
\]
For a smooth compactly supported spacetime function \(F\), Minkowski and the
interpolated dispersive estimate give
\[
\|TT^*F(t)\|_r
\le C_r\int|t-s|^{-2/q}\|F(s)\|_{r'}\,ds.
\]
Section I.1 with \(p=q'\) yields
\[
\|TT^*F\|_{L^q_tL^r_x}
\le A_{q,r}\|F\|_{L^{q'}_tL^{r'}_x}.
\]
This includes \((q,r)=(4,\infty)\).

Fubini, the group law, and unitarity give the quadratic identity
\[
\|T^*F\|_2^2
=\left|\iint (TT^*F)(t,x)\overline{F(t,x)}\,dx\,dt\right|.
\]
Mixed Hölder therefore gives
\[
\|T^*F\|_2\le A_{q,r}^{1/2}
\|F\|_{L^{q'}L^{r'}}.
\]
All exchanges of integrals are absolutely justified for the chosen tests;
the singular set \(t=s\) is null.

### II.3. Norming Schwartz free solutions

For Schwartz \(f\), first prove that \(S(t)f\) has finite target norm.  On
\(|t|\le1\), Fourier inversion gives a uniform \(L^\infty\) bound and
unitarity gives a uniform \(L^2\) bound.  On \(|t|>1\), spatial interpolation
between \(L^2\) and the dispersive \(L^\infty\) bound gives
\[
\|S(t)f\|_r\le C_f|t|^{-\alpha}.
\]
Since \(q\alpha=2\), the \(q\)-th power is integrable at infinity.

For every smooth compactly supported \(G\), put \(F=\overline G\).  With the
Hilbert inner product convention absorbed by conjugation,
\[
\left|\iint S(t)f(x)G(t,x)\,dx\,dt\right|
=|\langle f,T^*F\rangle|
\le A_{q,r}^{1/2}\|f\|_2\|G\|_{L^{q'}L^{r'}}.
\]
Use the density and norming statements of Section I.3.  This proves
\[
\|S(t)f\|_{L^qL^r}\le A_{q,r}^{1/2}\|f\|_2
\]
for Schwartz \(f\), including the scalar \(L^4_tL^\infty_x\) endpoint.

### II.4. Extension and identification for arbitrary L2 data

Choose Schwartz \(f_n\to f\) in \(L^2\).  The estimate applied to differences
and Section I.3 produce a jointly measurable mixed-norm limit \(H\).  On a
finite rectangle \(J\times K\), since \(q,r\ge2\),
\[
\|H_n-H\|_{L^2(J\times K)}
\le |J|^{1/2-1/q}|K|^{1/2-1/r}
\|H_n-H\|_{L^qL^r},
\]
where \(|K|^{1/2-1/\infty}=|K|^{1/2}\).  Hence \(H_n\to H\) locally in
spacetime \(L^2\).  Unitarity also gives
\[
\int_J\|S(t)(f_n-f)\|_2^2\,dt=|J|\|f_n-f\|_2^2\to0.
\]
Uniqueness of the \(L^2(J\times K)\) limit identifies \(H\) with the jointly
measurable representative of \(S(t)f\).  A countable exhaustion makes the
identity global.  Norm continuity gives the desired bound for \(f\).

Finally, admissibility has only the following cases: \(r=\infty\) forces
\(q=4\); \(r=2\) forces \(q=\infty\); otherwise \(2<r<\infty\) and
\(4<q<\infty\).  The \((\infty,2)\) case is exactly unitarity.  This completes
`hom_strichartz` without a project axiom.

## III. The lower-half-space zero extension

Write coordinates as \((t,s,r)\), matching the Lean product order.  Put
\[
F(t,s,r)=u(t,(r+s)/\sqrt2)v(t,(r-s)/\sqrt2)
-v(t,(r+s)/\sqrt2)u(t,(r-s)/\sqrt2)
\]
and let \(Q\) be the ridge potential.

### III.1. Local exterior equation from the mild equations

On every bounded time interval, the mild equation implies the distributional
NLS equation.  One direct proof is to test the Duhamel formula, use the group
law, and integrate by parts in the time variable; interval integrability of
the bundled nonlinearity and unitarity justify Fubini.  Equivalently, spatial
mollification gives a classical-in-space equation and converges in every
pairing.

The continuous bilinear map
\(L^2_x\times L^2_y\to L^2_{x,y}\) then gives the unfactored equation
\[
PF=\sigma\bigl[N(u)(x)v(y)+u(x)N(v)(y)
-N(v)(x)u(y)-v(x)N(u)(y)\bigr].
\]
On compact time intervals all four terms lie in \(L^2_{t,x,y}\): for example
\[
\|N(u)(x)v(y)\|_{L^2_{t,x,y}}^2
\le \|v\|_{L^\infty_tL^2_y}^2
\int\|u(t)\|_6^6\,dt<\infty.
\]
The local modulus hypothesis supplies \(|u|^2=|v|^2\) almost everywhere on
\(I\).  Algebraic factorization and the orthogonal coordinate change give
\[
(i\partial_t+\partial_s^2+\partial_r^2)F=QF
\quad\hbox{in }\mathcal D'(I\times\mathbb R^2),
\]
with \(F,QF\in L^2\) on compact time subintervals.

For cutoff limits one also needs control against Schwartz weights on an
unbounded time set.  This follows from the mild equation.  Spatial
regularization and the weak equation show that \(\|u(t)\|_2\) and
\(\|v(t)\|_2\) are constant: pair the regularized equation with the
regularized solution, take the real part, and remove the regularization.  The
Laplacian contribution is purely imaginary, while the cubic contribution is
real before multiplication by \(-i\).

Let the resulting uniform mass bound be \(M\).  On a time interval \(J\), the
homogeneous \((6,6)\) estimate and Minkowski applied to the oriented Duhamel
integral give
\[
\|u\|_{L^6(J\times\mathbb R)}
\le CM+C|\sigma|\,|J|^{1/2}
\|u\|_{L^6(J\times\mathbb R)}^3.
\]
A continuity/bootstrap argument gives a bound depending only on
\(M,\sigma\) when \(|J|\) is below a fixed positive length.  Dividing unit
intervals into finitely many such pieces gives a uniform bound on every unit
interval.  Consequently \(F\) and \(QF\) have uniform local \(L^2\) bounds on
unit time intervals.  Their pairings with a Schwartz function and its
derivatives are absolutely summable over the integer time intervals.  This
justifies time cutoffs tending to one even when \(I\) is unbounded.

### III.2. The local critical current and Wronskian

The needed trace theorem is local in time, so the hypothesis
`SameModulusOnSet I` is sufficient.  Here is a closed proof of the required
local Wronskian statement.

First, for every spatial cutoff \(\chi\) and bounded \(J\Subset I\),
\[
\chi u,\chi v\in L^2(J;H^{1/2}).
\]
For the homogeneous term, split the frequency integral into positive and
negative frequencies and set \(\omega=4\pi^2\xi^2\).  Plancherel in time gives
the pointwise Kato identity
\[
\||D|^{1/2}S(t)f(x)\|_{L^2_t}\le C\|f\|_2,
\]
uniformly in \(x\).  The commutator
\([|D|^{1/2},\chi]\) is \(L^2\)-bounded because
\[
\bigl||\xi|^{1/2}-|\eta|^{1/2}\bigr|
\le|\xi-\eta|^{1/2}
\]
and \(|\zeta|^{1/2}\widehat\chi(\zeta)\in L^1\).  Integrating over
\(\operatorname{supp}\chi\) proves local homogeneous smoothing.  For the
Duhamel term, Minkowski and time translation give
\[
\left\|\chi\int_{t_0}^tS(t-s)N(u(s))\,ds\right\|_{L^2_tH^{1/2}_x(J)}
\le C_{\chi,J}\|N(u)\|_{L^1_tL^2_x(J)},
\]
which is finite by the local \(L^6\) hypothesis.

The same argument with the homogeneous \((4,\infty)\) estimate gives
\[
u,v\in L^4(J;L^\infty_x)
\]
on every bounded \(J\).  Thus the good time slices below are locally bounded
as well as locally \(H^{1/2}\).

Next spatially mollify the distributional NLS equation.  The mollified field
satisfies the continuity equation with an error
\((N(u))*\rho_\epsilon-N(u*\rho_\epsilon)\), which tends to zero in
\(L^2_{t,x}\) because \(u*\rho_\epsilon\to u\) in \(L^6\).  The error paired
with a bounded primitive times the mollified solution tends to zero by
spacetime Hölder.  The localized smoothing convergence and the Gagliardo
definition of \(H^{1/2}\) pass the current term to the limit.  Thus, for
\(\phi\in C_c^\infty\), its bounded primitive
\(a(x)=\int_{-\infty}^x\phi\), and \(\eta\in C_c^\infty(I)\),
\[
-\int\eta'(t)\int a|u|^2
=2\int\eta(t)\,\operatorname{Im}
\langle u_x,\phi\overline u\rangle_{H^{-1/2},H^{1/2}}.
\]
The same holds for \(v\).  Equality of the densities makes the left sides
equal.  The real part of
\(\langle u_x,\phi\overline u\rangle\) is
\(-\frac12\int\phi'|u|^2\), so the complete complex quadratic currents agree.
A countable \(C^1\)-dense set of spatial tests, followed by the bound
\[
|\Lambda_t(\phi)|\le C
\bigl(\|\chi u(t)\|_{H^{1/2}}^2+
      \|\chi v(t)\|_{H^{1/2}}^2\bigr)
(\|\phi\|_\infty+\|\phi'\|_\infty),
\]
slices this equality at almost every time in \(I\).

At each good time localize by a real cutoff and write \(f=\chi u\),
\(g=\chi v\).  They lie in \(H^{1/2}\cap L^\infty\), have the same modulus,
and have equal quadratic current.  Put
\[
\rho=|f|^2=|g|^2,
\quad s_\epsilon=\frac\rho{\rho+\epsilon},
\quad h_\epsilon=\frac{fg}{\rho+\epsilon}.
\]
The Gagliardo product inequality shows that
\(H^{1/2}\cap L^\infty\) is an algebra.  Lipschitz composition shows that
\(s_\epsilon,h_\epsilon\in H^{1/2}\cap L^\infty\).  For the reciprocal in
\(h_\epsilon\), multiply by a compact cutoff equal to one on the supports of
\(f,g\), and write
\[
(\rho+\epsilon)^{-1}=\epsilon^{-1}
+[(\rho+\epsilon)^{-1}-\epsilon^{-1}].
\]
The bracket is a Lipschitz function of \(\rho\) which vanishes at zero.
Testing current equality
with \(h_\epsilon\phi\) gives
\[
\langle f',s_\epsilon g\phi\rangle
-\langle g',s_\epsilon f\phi\rangle=0.
\]
Therefore
\[
\langle gf'-fg',\phi\rangle
=\langle f',T_\epsilon(g)\phi\rangle
-\langle g',T_\epsilon(f)\phi\rangle,
\qquad
T_\epsilon(z)=\frac{\epsilon z}{|z|^2+\epsilon}.
\]
The radial map \(T_\epsilon\) is one-Lipschitz, is bounded by
\(\sqrt\epsilon/2\), and converges pointwise to zero.  Dominated convergence
in the Gagliardo double integral and in \(L^2\) gives
\(T_\epsilon(f),T_\epsilon(g)\to0\) in \(H^{1/2}\).  Hence
\[
gf'-fg'=0
\]
as a spatial distribution for almost every time in \(I\).

### III.3. Scalar traces

For a compactly supported smooth \(\psi(t,r)\) with time support in \(I\), set
\[
H_\psi(s)=\iint F(t,s,r)\psi(t,r)\,dt\,dr.
\]
Define
\[
A_\psi(s)=\iint F(-i\psi_t+\psi_{rr}),
\qquad
K_\psi(s)=\iint QF\psi.
\]
Cauchy--Schwarz gives \(H_\psi,A_\psi,K_\psi\in L^2_{\rm loc}(ds)\), and the
weak exterior equation gives
\[
H_\psi''=K_\psi-A_\psi.
\]
Mollify in \(s\) on nested intervals.  The identity
\[
\int\chi^2|h'|^2
=-\operatorname{Re}\int\chi^2h''\overline h
-2\operatorname{Re}\int\chi\chi'h'\overline h
\]
and \(2ab\le\frac12a^2+2b^2\) give a uniform interior \(H^1\) bound for the
mollifications.  Weak compactness identifies the derivative, proving
\(H_\psi\in H^2_{\rm loc}\).  The one-dimensional fundamental theorem and
Cauchy--Schwarz give its unique \(C^1\) representative.

Oddness of \(F\) in \(s\) gives
\[
H_\psi(0)=0.
\]

For the Neumann trace, put \(z=(r-s)/\sqrt2\).  Then
\[
H_\psi(s)=\sqrt2\iint
[u(t,z+\sqrt2s)v(t,z)-v(t,z+\sqrt2s)u(t,z)]
\psi(t,\sqrt2z+s)\,dz\,dt.
\]
Choose nested cutoffs \(\chi_0,\chi_1\) equal to one on all spatial points
appearing for \(|s|\le s_0\).  Set
\[
\widetilde D_su=
\frac{(\chi_1u)(\cdot+\sqrt2s)-\chi_1u}{s},
\]
and similarly for \(v\).  Fourier multiplication gives
\[
\widetilde D_su\to\sqrt2(\chi_1u)_x
\quad\text{in }L^2_tH^{-1/2}_x,
\]
with a uniform bound by \(C\|\chi_1u\|_{L^2_tH^{1/2}}\).  If
\(\psi_s(t,z)=\psi(t,\sqrt2z+s)\), the mean-value theorem in the Gagliardo
seminorm gives
\[
\|(\psi_s-\psi_0)f\|_{H^{1/2}}
\le C_\psi|s|\|f\|_{H^{1/2}}.
\]
The exact difference-quotient identity is
\[
\frac{H_\psi(s)}s=\sqrt2\int
\bigl(\langle\widetilde D_su,v\psi_s\rangle
-\langle\widetilde D_sv,u\psi_s\rangle\bigr)\,dt.
\]
Replacing \(\psi_s\) by \(\psi_0\) costs \(O(|s|)\) by Cauchy--Schwarz in
time.  Passing to the limit and removing \(\chi_1\), which is one near the
test support, gives
\[
H_\psi'(0)=2\int
\langle vu_x-uv_x,\psi(t,\sqrt2\,\cdot)\rangle\,dt=0
\]
by the local Wronskian result.

For an arbitrary Schwartz \(\psi\), multiply by compact cutoffs tending to
one.  The interior \(H^2\) estimate above bounds
\(|H_\psi(0)|+|H_\psi'(0)|\) by finitely many Schwartz seminorms of \(\psi\)
times weighted \(L^2\) norms of \(F,QF\).  The uniform unit-interval bounds
proved in III.1 make these weights summable in time; spatial summability is
immediate from the \(L^2\) bounds and Schwartz decay.  Therefore the
compact-support result passes to Schwartz tests, including tests with
unbounded time support inside an unbounded open set.

### III.4. The jump calculation and general tests

For \(h\in H^2_{\rm loc}\), two integrations by parts give
\[
\int_{-\infty}^0h\varphi''
=\int_{-\infty}^0h''\varphi-h'(0)\varphi(0)+h(0)\varphi'(0).
\]
Equivalently,
\[
(\mathbf1_{s<0}h)''
=\mathbf1_{s<0}h''-h'(0)\delta_0-h(0)\delta'_0.
\]

For a separated test \(\Psi(t,s,r)=\psi(t,r)\varphi(s)\), the weak left side
for \(G=\mathbf1_{s<0}F\) is
\[
\int_{s<0}A_\psi(s)\varphi(s)\,ds
+\int_{s<0}H_\psi(s)\varphi''(s)\,ds.
\]
Using \(H_\psi''=K_\psi-A_\psi\) and both zero traces, this equals
\[
\int_{s<0}K_\psi(s)\varphi(s)\,ds,
\]
which is exactly the weak pairing with
\(\mathbf1_{s<0}QF\).

It remains to pass to an arbitrary Schwartz test while preserving its time
support.  First multiply in the \(s\)-variable by a cutoff \(\chi_R(s)\);
this converges in Schwartz topology and does not change time support.  Periodize
the compactly \(s\)-supported function on a larger \(s\)-interval.  Its Fourier
coefficients
\[
\psi_k(t,r)=\frac1L\int\chi_R(s)\Psi(t,s,r)e^{-2\pi iks/L}\,ds
\]
are Schwartz in \((t,r)\) and vanish whenever \(t\notin I\).  Repeated
integration by parts in \(s\) makes the coefficients rapidly decreasing in
every Schwartz seminorm.  Thus the finite sums
\[
\sum_{|k|\le N}\psi_k(t,r)\kappa_R(s)e^{2\pi iks/L}
\]
converge in Schwartz topology and are separated tests with the same time
support condition.  Continuity of the \(L^2\) pairings permits the limit.
This proves `zero_extension_jump` with the lower-half-space convention.

## IV. Quantitative one-step propagation

### IV.1. The one-slab theorem from the corrected Carleman inverse

The multiplier estimate follows directly from Hölder.  If
\(W=W_1+W_2\), then
\[
\|W_1Z\|_{L^1_tL^2_z}
\le\|W_1\|_{L^1_tL^\infty_z}\|Z\|_{L^\infty_tL^2_z},
\]
and
\[
\|W_2Z\|_{L^{4/3}_{t,z}}
\le\|W_2\|_2\|Z\|_4.
\]
Taking the infimum over decompositions proves
\(\|WZ\|_X\le\|W\|_Y\|Z\|_{X'}\).

For \(P_\beta=e^{\beta z_1}Pe^{-\beta z_1}\), use the corrected frequency
coefficient
\[
a_\beta(\xi)=\beta^2-4\pi^2|\xi|^2,
\qquad b_\beta(\xi)=4\pi\beta\xi_1.
\]
Solve the scalar time ODE forward for \(\xi_1<0\) and backward for
\(\xi_1>0\).  The resulting time-increment multiplier is supported where
\(\tau\xi_1<0\), has oscillation \(e^{ia_\beta(\xi)\tau}\), and damping
\(e^{b_\beta(\xi)\tau}\), whose modulus is at most one.

Plancherel gives the \(L^2\)-operator bound.  The inverse Fourier kernel
factorizes.  The full \(\xi_2\)-Gaussian has modulus \(C|\tau|^{-1/2}\).  After
reflection and scaling, the \(\xi_1\) factor is
\[
|\tau|^{-1/2}\int_0^\infty e^{i(Ay\pm y^2)}e^{-By}\,dy,
\qquad B\ge0.
\]
This integral is uniformly bounded.  Split where the derivative of the phase
has modulus at most one; that set has bounded length.  On each of the at most
two complementary intervals integrate by parts with
\(e^{i\phi}=(i\phi')^{-1}(e^{i\phi})'\).  Boundary terms, the derivative of
the amplitude, and the variation of \(1/\phi'\) are all uniformly bounded.
For \(B=0\), one further integration by parts on a tail proves convergence of
the improper integral.  Gaussian regularization justifies the Fourier
inversion before the limit.  Hence
\[
\|K_\beta(\tau)\|_{L^1\to L^\infty}\le C|\tau|^{-1}.
\]
Section I.2 gives the \(L^{4/3}\to L^4\) bound
\(C|\tau|^{-1/2}\).

A TT-star argument, using Section I.1 with exponent \(1/2\), yields the
uniform homogeneous estimate
\[
\|K_\beta(t-s)g\|_{L^4_{t,z}}+
\|K_\beta(t-s)^*g\|_{L^4_{t,z}}\le C\|g\|_2.
\]
Minkowski, HLS, and duality then give all four mappings
\[
T_\beta:L^1_tL^2_z+L^{4/3}_{t,z}
\longrightarrow L^\infty_tL^2_z\cap L^4_{t,z}.
\]

For a compact-time weak graph solution, spatial mollification puts the source
in \(L^1_tL^2_z\).  Spatial Fourier transform and Fubini slice the equation at
almost every frequency.  A scalar distributional ODE whose derivative is
locally \(L^1\) has an absolutely continuous representative; compact time
support selects the forward/backward formula above.  Removing the mollifier
in \(X\), and using uniqueness of distributional limits, proves the graph
Carleman estimate
\[
\|e^{\beta z_1}U\|_{X'}
\le C_C\|e^{\beta z_1}PU\|_X.
\]

Combining this with the multiplier bound, choose
\(\varepsilon_*=(2C_C)^{-1}\) (or the corresponding product if the multiplier
constant is not normalized to one).  If
\(PU=VU+R\) and \(\|V\|_Y\le\varepsilon_*\), absorption gives
\[
\|e^{\beta z_1}U\|_{X'}
\le2C_C\|e^{\beta z_1}R\|_X.
\]
On \(z_1>0\) the exponential is at least one.  If the right side tends to
zero, then \(U=0\) there.  This is the one-slab theorem.

### IV.2. Explicit compatible cutoffs

Fix a smooth step \(\rho\) with
\[
0\le\rho\le1,\quad \rho(x)=0\ (x\le0),\quad
\rho(x)=1\ (x\ge1).
\]
Put
\[
\ell(t)=\rho\!\left(\frac{t-a-2\delta}{\delta}\right),
\qquad
r(t)=\rho\!\left(\frac{b-2\delta-t}{\delta}\right),
\qquad
\omega(t)=2-3\ell(t)r(t).
\]
Since \(\delta<(b-a)/8\), the transition intervals are disjoint.  Hence
\[
\omega=2\text{ on }(-\infty,a+2\delta]\cup[b-2\delta,\infty),
\quad
\omega=-1\text{ on }[a+3\delta,b-3\delta],
\]
and, with a constant depending only on \(\rho\),
\[
\|\omega''\|_{L^1}\le K_\rho/\delta.
\]
Also set
\[
\eta(t)=
\rho\!\left(\frac{t-a-\delta}{\delta}\right)
\rho\!\left(\frac{b-\delta-t}{\delta}\right).
\]
Then \(\eta\) is compactly supported in \((a,b)\), equals one on
\([a+2\delta,b-2\delta]\), and \(\operatorname{supp}\eta'\) lies where
\(\omega=2\).  Moreover \(\|\eta'\|_1\) is bounded solely in terms of
\(\rho\).

Set \(w=B+h\omega\).  In translated coordinates
\[
V(t,y)=Z(t,y_1+w(t),y_2),
\]
the known support gives
\[
V=0\quad\text{if }y_1>-h\omega(t).
\]
Thus \(V=0\) for \(y_1>h\) everywhere, and on
\(\operatorname{supp}\eta'\) it vanishes already for \(y_1>-2h\).

### IV.3. Galilean gauge and the exact error

Let
\[
\gamma(t)=\frac{w'(t)}2,
\qquad
U(t,y)=
e^{-i\gamma(t)y_1-i\int_a^t\gamma(s)^2ds}V(t,y).
\]
A change of variables in the weak pairing proves
\[
PV=W(t,y_1+w(t),y_2)V+iw'(t)\partial_{y_1}V.
\]
The distributional product rule for the smooth phase cancels the first-order
term and gives
\[
PU=\left(W(t,y_1+w(t),y_2)+\frac{w''(t)}2y_1\right)U.
\]
Spatial translation and the unimodular phase preserve both components of the
\(X'\)-norm.  They also preserve all relevant almost-everywhere statements:
Fubini reduces this to translation invariance of spatial Lebesgue measure at
each fixed time.  No differentiability of a null-set representative is used.

Put \(Y=\eta U\) and define
\[
A_{\rm near}(t,y)=\frac{w''(t)}2y_1
\mathbf1_{\{-h<y_1\le h\}},
\qquad
A_{\rm far}(t,y)=\frac{w''(t)}2y_1
\mathbf1_{\{y_1\le-h\}}.
\]
Use the globally controlled potential
\[
\widetilde V(t,y)=
\mathbf1_{(a,b)}(t)W(t,y_1+w(t),y_2)+A_{\rm near}(t,y).
\]
Because \(U=0\) for \(y_1>h\), the exact global equation is
\[
PY=\widetilde VY+R,
\qquad
R=\eta A_{\rm far}U+i\eta'U.
\]

The near coefficient satisfies
\[
\|A_{\rm near}\|_{L^1_tL^\infty_y}
\le\frac h2\|w''\|_1
\le\frac{K_\rho}{2}\frac{h^2}{\delta}.
\]
Choose a real \(e>0\) with \(\operatorname{ofReal}(e)\le\varepsilon_*\), and
then choose
\[
c_0\le\min\left\{1,\frac{e}{2(1+K_\rho/2)}\right\}.
\]
If \(h\le c_0\sqrt\delta\), then
\[
\|\widetilde V\|_Y
\le c_0+(K_\rho/2)c_0^2\le e\le\varepsilon_*.
\]

### IV.4. Weighted decay, with the missing moment factor retained

Restrict \(U\) to \((a,b)\) when forming the error; this gives a global
\(L^\infty_tL^2_y\) field without changing \(R\).  Let its norm be \(M\).
For \(\beta>0\),
\[
\sup_{y_1\le-h}|y_1|e^{\beta y_1}
\le e^{-\beta h}(h+\beta^{-1}).
\]
Indeed write \(-y_1=h+q\) and use
\(q e^{-\beta q}\le1/(e\beta)\).  Therefore
\[
\|e^{\beta y_1}\eta A_{\rm far}U\|_{L^1_tL^2_y}
\le M\left\|\eta\frac{w''}2\right\|_1
e^{-\beta h}(h+\beta^{-1})\longrightarrow0.
\]
On \(\operatorname{supp}\eta'\), the stronger support bound gives
\[
\|e^{\beta y_1}\eta'U\|_{L^1_tL^2_y}
\le M\|\eta'\|_1e^{-2\beta h}\longrightarrow0.
\]
A pure \(L^1_tL^2_y\) source has \(X\)-norm no larger than that norm, so the
one-slab error hypothesis holds.

The one-slab theorem yields \(Y=0\) for \(y_1>0\).  On
\((a+4\delta,b-4\delta)\), one has \(\eta=1\) and \(\omega=-1\), hence
\(w=B-h\).  Thus \(y_1>0\) is exactly \(z_1>B-h\).  Pulling the almost-everywhere
statement back by the fixed spatial translation on this central interval
proves `one_step_propagation`.

## V. Formalization consequence

The three target theorems now have closed mathematical proofs.  A literal
mathlib-only Lean implementation still has to formalize the shared lemmas
above and the lower Carleman/trace infrastructure; invoking their present
project declarations would merely move the axiom frontier.  In addition, the
Carleman inverse and its weak-equation interface must be corrected before its
identification theorem can be proved.  No further conceptual mathematical
input is needed for the three target statements beyond the arguments in this
note.
