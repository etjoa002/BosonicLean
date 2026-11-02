# The sealed statements

Generated from `verify/Challenge.lean` by `verify/make_core_page.py`: the 115 statements that `lake comparator` checks (see the section "Verification" of the front page). Each entry gives the statement in words and the name of its formal version in `Challenge.lean`.

## Covariance matrices

A phase-space index of $`n`$ modes is an element of $`\mathrm{Fin}\, n \oplus \mathrm{Fin}\, n`$: the positions $`q_1, \dots, q_n`$ followed by the momenta $`p_1, \dots, p_n`$. A real matrix is regarded as a complex matrix entrywise, and a complex matrix $`H`$ is positive semidefinite, $`H \ge 0`$, when it is Hermitian with $`\bar x^T H x \ge 0`$ for every complex vector $`x`$.

**1.** The standard symplectic matrix on $`n`$ modes is 

```math
\Omega = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}
```

in the blocks of positions and momenta.  
<sub>`Sealed.symplecticForm_eq`</sub>

**2.** A real $`2n \times 2n`$ matrix $`\gamma`$ is an admissible covariance matrix if and only if it is symmetric and $`\gamma - i\Omega \ge 0`$.  
<sub>`Sealed.isAdmissible_iff`</sub>

**3.** Symplectic congruence: a real $`2n \times 2n`$ matrix $`S`$ is symplectic when $`S \Omega S^T = \Omega`$. If $`\gamma`$ is admissible and $`S`$ is symplectic, then $`S \gamma S^T`$ is admissible.  
<sub>`Sealed.isAdmissible_symplectic_congr`</sub>

**4.** Restriction to a set of modes: if $`\gamma`$ is admissible on $`n`$ modes and $`e`$ is an injective map from $`m`$ modes to the $`n`$ modes, the matrix with entries $`\gamma(e(a), e(b))`$, positions going to positions and momenta to momenta, is admissible on $`m`$ modes.  
<sub>`Sealed.isAdmissible_restrict`</sub>

**5.** Independent sums: for $`\gamma_1`$ on $`n`$ modes and $`\gamma_2`$ on $`m`$ modes, the block-diagonal matrix $`\gamma_1 \oplus \gamma_2`$ on $`n + m`$ modes, in which the first $`n`$ modes carry $`\gamma_1`$ and the last $`m`$ modes carry $`\gamma_2`$, is admissible if and only if $`\gamma_1`$ and $`\gamma_2`$ are.  
<sub>`Sealed.isAdmissible_directSum_iff`</sub>

**6.** One mode: the diagonal matrix $`\mathrm{diag}(a, b)`$ is admissible if and only if $`a > 0`$ and $`ab \ge 1`$.  
<sub>`Sealed.isAdmissible_diagonal_iff`</sub>

**7.** Every admissible matrix $`\gamma`$ is positive definite: $`x^T \gamma x > 0`$ for every nonzero real vector $`x`$.  
<sub>`Sealed.posDef_of_isAdmissible`</sub>

## The Gaussian wave function

Admissibility, $`\gamma - i\Omega \ge 0`$, is the uncertainty relation in units with $`\hbar = 1`$. By entry 6, the covariance $`\mathrm{diag}(s^2, \hbar^2/s^2)`$ of the next entry is admissible exactly when $`\hbar \ge 1`$; with $`\hbar = 1`$ it is $`\mathrm{diag}(s^2, 1/s^2)`$, admissible for every $`s > 0`$.

**8.** Let $`s > 0`$, $`\hbar > 0`$ and 

```math
\psi(x) = (\sqrt{\pi}\, s)^{-1/2} e^{-x^2/(2s^2)}
```

on $`\mathbb R`$. Then $`\int |\psi|^2\, dx = 1`$. Let $`A_q \psi = x\psi`$ and $`A_p \psi = -i\hbar\psi'`$ be the position and momentum applied to $`\psi`$, 

```math
m_j = \mathrm{Re} \int \bar\psi\, A_j\psi\, dx
```

their means, and 

```math
\gamma_{jk} = 2\, \mathrm{Re} \int \overline{(A_j\psi - m_j\psi)}\, (A_k\psi - m_k\psi)\, dx
```

for $`j, k \in \{q, p\}`$. Then $`\gamma = \mathrm{diag}(s^2, \hbar^2/s^2)`$.  
<sub>`Sealed.gaussian_wave_function`</sub>

## Contraction and periodic chains

A Gaussian matrix product state is obtained from an independent covariance matrix of physical and virtual modes by eliminating the virtual modes, which is a Schur complement.

**9.** The contraction: for a real $`2n \times 2n`$ matrix $`\gamma`$ and a real matrix $`K`$ with $`k + 2m`$ rows and $`2n`$ columns, let $`V = K \gamma K^T`$ with blocks $`E`$ (the first $`k`$ rows and columns), $`F`$ (the first $`k`$ rows, the last $`2m`$ columns), $`F'`$ (the last $`2m`$ rows, the first $`k`$ columns) and $`G`$ (the last $`2m`$ rows and columns). The contracted covariance is the Schur complement $`G - F' E^{-1} F`$, where $`E^{-1}`$ is the matrix inverse ($`E`$ is invertible by the next statement).  
<sub>`Sealed.contractCovariance_eq`</sub>

**10.** Contraction preserves admissibility: let $`\gamma`$ be admissible on $`n`$ modes and $`K`$ a real matrix with $`k + 2m`$ rows and $`2n`$ columns whose rows are linearly independent ($`K^T`$ is injective) and with 

```math
K \Omega K^T = \begin{pmatrix} 0 & 0 \\ 0 & \Omega \end{pmatrix},
```

the lower right block being the symplectic matrix of $`m`$ modes. Then the block $`E`$ of $`K\gamma K^T`$ is positive definite and the contracted covariance is admissible on $`m`$ modes.  
<sub>`Sealed.isAdmissible_contractCovariance`</sub>

**11.** The input of a periodic chain: $`N`$ sites, each with $`2M + 1`$ local modes, and real $`2(2M+1) \times 2(2M+1)`$ matrices $`\Gamma_j`$, one for each site $`j`$. Mode $`l`$ of site $`j`$ is the global mode $`(2M+1) j + l`$. The input matrix is block diagonal: its entry between the global coordinates of the local coordinates $`u`$ of site $`j`$ and $`v`$ of site $`j'`$ is $`\Gamma_j(u, v)`$ if $`j = j'`$ and $`0`$ otherwise.  
<sub>`Sealed.periodicInput_apply`</sub>

**12.** The wiring of a periodic chain: each site $`i`$ of $`N`$ has $`M`$ virtual modes $`A_{i,a}`$ (local modes $`0, \dots, M-1`$), $`M`$ virtual modes $`B_{i,a}`$ (local modes $`M, \dots, 2M-1`$) and one physical mode $`C_i`$ (local mode $`2M`$), numbered globally as for the input. The wiring matrix $`K`$ has $`2NM`$ rows to be eliminated followed by $`2N`$ rows for the physical modes. Write $`e_x`$ for the standard basis vector of the global coordinate $`x`$, and $`i - 1`$ for the site before $`i`$, cyclically (the inverse of the rotation $`j \mapsto j + 1 \bmod N`$). For each site $`i`$ and $`a < M`$, the row $`Mi + a`$ of $`K`$ is $`e_{q(A_{i,a})} + e_{q(B_{i-1,a})}`$ and the row $`NM + Mi + a`$ is $`e_{p(A_{i,a})} - e_{p(B_{i-1,a})}`$ (each bond is wired as a maximally entangled pair); the rows of the physical mode of site $`i`$ are $`e_{q(C_i)}`$ and $`e_{p(C_i)}`$.  
<sub>`Sealed.periodicWiring_rows`</sub>

**13.** Periodic chains: let $`N \ge 3`$ and $`M \ge 1`$, and let every $`\Gamma_j`$ be admissible on $`2M + 1`$ modes. Then the wiring $`K`$ has linearly independent rows and satisfies 

```math
K \Omega K^T = \begin{pmatrix} 0 & 0 \\ 0 & \Omega \end{pmatrix}
```

(the symplectic matrix of the $`N`$ physical modes in the lower right block), the eliminated block of $`K \gamma K^T`$ for the input matrix $`\gamma`$ is positive definite, and the contracted covariance of the $`N`$ physical modes is admissible.  
<sub>`Sealed.isAdmissible_periodic`</sub>

## The CCR algebra

$`V`$ is a real vector space and $`\sigma`$ a real bilinear form on $`V`$. The form $`\sigma`$ is alternating when $`\sigma(u, u) = 0`$ for every $`u`$. It is nondegenerate when $`\sigma(u, \cdot) = 0`$ only for $`u = 0`$ and $`\sigma(\cdot, w) = 0`$ only for $`w = 0`$; for alternating $`\sigma`$ the two conditions coincide. The Hilbert space $`\ell^2(V)`$ consists of the functions $`f : V \to \mathbb C`$ with 

```math
\sum_{v \in V} |f(v)|^2 < \infty,
```

that is, $`\ell^2`$ of $`V`$ with the discrete topology; bounded operators carry the operator norm and the adjoint as star. The matrix $`\Omega`$ of the covariance sections is the matrix of $`\sigma`$ in the coordinates $`(q, p)`$ of $`V = \mathbb R^{2n}`$, $`\sigma(u, w) = u^T \Omega w`$ with $`\Omega`$ as in entry 1; on one mode this is the form $`\sigma(u, w) = u_1 w_2 - u_2 w_1`$ of entry 32.

**14.** The Weyl operators and the CCR algebra: let $`\sigma`$ be any real bilinear form on $`V`$. For $`u \in V`$ the Weyl operator $`W(u)`$ is the bounded operator on $`\ell^2(V)`$ with 

```math
(W(u) f)(v) = e^{i\sigma(u, v)/2} f(v + u),
```

and the CCR algebra $`\mathrm{CCR}(V, \sigma)`$ is the norm closure of the star subalgebra generated by the Weyl operators.  
<sub>`Sealed.weyl_apply_and_CCR_eq`</sub>

**15.** For alternating $`\sigma`$, every Weyl operator is unitary, $`W(u)^* = W(-u)`$, and the Weyl relation 

```math
W(u) W(w) = e^{-i\sigma(u, w)/2} W(u + w)
```

holds.  
<sub>`Sealed.weyl_relations`</sub>

**16.** Relabelling: let $`\sigma`$ and $`\sigma'`$ be any real bilinear forms on $`V`$ and $`V'`$. For a linear bijection $`T : V \to V'`$ with $`\sigma'(Tu, Tv) = \sigma(u, v)`$ there is a $`\mathbb C`$-linear star isomorphism $`\varphi : \mathrm{CCR}(V, \sigma) \to \mathrm{CCR}(V', \sigma')`$ with $`\varphi(W(u)) = W'(Tu)`$ for every $`u \in V`$.  
<sub>`Sealed.exists_starAlgEquiv_relabel`</sub>

**17.** Simplicity: for alternating nondegenerate $`\sigma`$, the CCR algebra is a simple ring: its only two-sided ideals are $`0`$ and the whole algebra, and these differ.  
<sub>`Sealed.isSimpleRing_CCR`</sub>

**18.** Automorphisms of Weyl type: let $`\sigma`$ be alternating and nondegenerate, $`T`$ a $`\mathbb C`$-linear star automorphism of $`\mathrm{CCR}(V, \sigma)`$, $`\Gamma : V \to V`$ and $`c : V \to \mathbb C`$ with $`T(W(u)) = c(u) W(\Gamma u)`$ for every $`u`$. Then $`\Gamma`$ is a real-linear bijection preserving $`\sigma`$, and $`c`$ is a character of modulus one: $`c(u + w) = c(u) c(w)`$ and $`|c(u)| = 1`$.  
<sub>`Sealed.weyl_automorphism`</sub>

## States and Gaussian states

A state on $`\mathrm{CCR}(V, \sigma)`$ is a continuous complex-linear functional $`\omega`$ with $`\omega(1) = 1`$ and $`\omega(a^* a) \ge 0`$ for every $`a`$ (a real non-negative number). Its characteristic function is $`u \mapsto \omega(W(u))`$.

**19.** Determination by the characteristic function: let $`\sigma`$ be alternating. Two continuous complex-linear functionals on $`\mathrm{CCR}(V, \sigma)`$, in particular two states, that agree on every Weyl operator are equal; so a state is determined by its characteristic function.  
<sub>`Sealed.eq_of_charFun`</sub>

**20.** A necessary condition for Gaussian states: let $`\sigma`$ be alternating and $`\omega`$ a state on $`\mathrm{CCR}(V, \sigma)`$ that is Gaussian with symmetric covariance form $`\gamma`$ and linear displacement $`d`$, that is 

```math
\omega(W(u)) = \exp(i d(u) - \gamma(u, u)/4)
```

for every $`u`$. Then the data $`(d, \gamma)`$ satisfy all three of the following: (i) $`\gamma + i\sigma \ge 0`$, that is, for every finite family $`u_1, \dots, u_m`$ of vectors the complex matrix $`(\gamma(u_j, u_k) + i \sigma(u_j, u_k))_{jk}`$ is positive semidefinite; (ii) $`\gamma(u, u) \ge 0`$ for every $`u`$; (iii) $`\sigma(u, w)^2 \le \gamma(u, u) \gamma(w, w)`$ for all $`u, w`$. Conditions (ii) and (iii) follow from (i) with $`m = 1`$ and $`m = 2`$. The condition is necessary: every Gaussian state has data satisfying it. The existence of a Gaussian state for data satisfying the condition is a candidate for a later theorem.  
<sub>`Sealed.gaussian_state_condition`</sub>

## Gaussian channels

A Gaussian channel on $`\mathrm{CCR}(V, \sigma)`$ has data $`(L, \nu, \mu)`$: a linear map $`L : V \to V`$, a symmetric bilinear form $`\nu`$ and a linear form $`\mu`$, satisfying the channel condition $`\nu + i\sigma - i\sigma(L\cdot, L\cdot) \ge 0`$ (every finite Gram matrix positive semidefinite), together with a completely positive map $`f`$ of the CCR algebra with 

```math
f(W(u)) = \exp(i\mu(u) - \nu(u, u)/4)\, W(Lu).
```

A complex-linear map $`f`$ of the CCR algebra is completely positive when every matrix amplification $`(a_{jk}) \mapsto (f(a_{jk}))`$ on $`k \times k`$ matrices with entries in the CCR algebra is positive. The order on the CCR algebra is that of the bounded operators. Complete positivity of the maps is a hypothesis.

**21.** Composition: let $`\sigma`$ be any real bilinear form on $`V`$, and let $`(L_1, \nu_1, \mu_1, f_1)`$ and $`(L_2, \nu_2, \mu_2, f_2)`$ be Gaussian channels. Then $`a \mapsto f_2(f_1(a))`$ is completely positive and is the Gaussian channel with data $`L = L_2 L_1`$, $`\nu = \nu_1 + \nu_2(L_1\cdot, L_1\cdot)`$ and $`\mu = \mu_1 + \mu_2 \circ L_1`$: $`\nu`$ is symmetric, the data satisfy the channel condition, and 

```math
f_2(f_1(W(u))) = \exp(i\mu(u) - \nu(u, u)/4)\, W(Lu).
```  
<sub>`Sealed.gaussianChannel_comp`</sub>

**22.** Channel matrices: for $`n`$ modes, let $`X`$ and $`Y`$ be real $`2n \times 2n`$ matrices with $`Y`$ symmetric and $`Y - i\Omega + iX\Omega X^T \ge 0`$. Then $`X \gamma X^T + Y`$ is admissible for every admissible $`\gamma`$.  
<sub>`Sealed.isAdmissible_channel`</sub>

## The formal Fock space

The modes form a type $`\iota`$, an occupation-number configuration is a finitely supported $`n : \iota \to \mathbb N`$ (finitely supported), with $`|n| = \sum_i n_i`$ and $`n! = \prod_i n_i!`$, and $`e_i`$ is the configuration with one particle in mode $`i`$. The coefficients lie in a complex vector space $`R`$, which for the Bargmann map and in entry 34 is a ring and a complex algebra. A complex-linear map $`T`$ of the formal Fock space raises the particle number if $`\psi(n) = 0`$ for all $`|n| < k`$ implies $`(T\psi)(n) = 0`$ for all $`|n| < k + 1`$. Entry 25 characterizes these maps and defines their exponential.

**23.** The formal Fock space is the space of all coefficient families: $`\psi \mapsto (\psi(n))_n`$ is a complex-linear bijection from the formal Fock space onto all functions from occupation numbers to $`R`$, with no summability condition. The creation operator is 

```math
(a_i^\dagger \psi)(n) = \sqrt{n_i}\, \psi(n - e_i)
```

if $`n_i > 0`$ and $`0`$ otherwise, and the annihilation operator is 

```math
(a_i \psi)(n) = \sqrt{n_i + 1}\, \psi(n + e_i).
```  
<sub>`Sealed.formalFock_and_ladder`</sub>

**24.** The canonical commutation relations on the whole formal Fock space: $`[a_i, a_j^\dagger] = \delta_{ij}`$, $`[a_i, a_j] = 0`$ and $`[a_i^\dagger, a_j^\dagger] = 0`$.  
<sub>`Sealed.ccr_ladder`</sub>

**25.** Operators that raise the particle number, and their exponential: a linear map $`T`$ of the formal Fock space raises the particle number if and only if, whenever $`\psi(n) = 0`$ for all $`|n| < k`$, also $`(T\psi)(n) = 0`$ for all $`|n| < k + 1`$. For such an operator $`T`$ the exponential is 

```math
(e^T \psi)(n) = \sum_{k=0}^{|n|} (T^k \psi)(n) / k!,
```

a finite sum.  
<sub>`Sealed.numberRaisingOp_and_exp`</sub>

**26.** The exponential law: for operators $`S`$ and $`T`$ that raise the particle number and whose underlying maps commute, the operator $`S + T`$ has as underlying map the sum of theirs, and $`e^{S+T} = e^S e^T`$.  
<sub>`Sealed.numberRaisingOp_exp_add`</sub>

**27.** The Bargmann map $`\mathfrak B`$ sends $`\psi`$ to the formal power series $`\sum_n \psi(n)\, z^n / \sqrt{n!}`$; it is, by its type, a complex-linear bijection onto all formal power series in variables $`z_i`$ ($`i \in \iota`$) with coefficients in $`R`$.  
<sub>`Sealed.coeff_toBargmann`</sub>

**28.** The Bargmann map turns $`a_j^\dagger`$ into multiplication by $`z_j`$ and $`a_j`$ into the partial derivative $`\partial_j = \partial / \partial z_j`$ defined on coefficients by 

```math
(\partial_j f)_n = (n_j + 1)\, f_{n + e_j}.
```  
<sub>`Sealed.toBargmann_ladder`</sub>

## Examples

These examples show that the hypotheses of the main theorems can be met and that the objects are not degenerate.

**29.** The vacuum $`\gamma = 1`$ is admissible on every number of modes; on one mode the squeezed matrix $`\mathrm{diag}(r, 1/r)`$ is admissible for every $`r > 0`$, and $`\mathrm{diag}(1/2, 1/2)`$ is not admissible.  
<sub>`Sealed.witness_admissible`</sub>

**30.** The attenuator: for $`0 \le \eta \le 1`$ the matrices $`X = \sqrt\eta\, 1`$ and $`Y = (1 - \eta)\, 1`$ on $`n`$ modes satisfy the hypotheses of the channel-matrix statement: $`Y`$ is symmetric and $`Y - i\Omega + iX\Omega X^T \ge 0`$.  
<sub>`Sealed.witness_attenuator`</sub>

**31.** An explicit three-site chain: with 

```math
C = \begin{pmatrix} 0 & 0 & 1 \\ 0 & 0 & 1 \\ 1 & 1 & 0 \end{pmatrix}
```

and 

```math
S = \begin{pmatrix} 1 & 0 \\ C & 1 \end{pmatrix},
```

every site of the periodic chain with $`N = 3`$ and $`M = 1`$ carries the local matrix $`S S^T`$, and the contracted covariance of the three physical modes is $`\Gamma_q \oplus \Gamma_p`$, with the position block 

```math
\Gamma_q = \frac15 \begin{pmatrix} 3 & 1 & 1 \\ 1 & 3 & 1 \\ 1 & 1 & 3 \end{pmatrix}
```

and the momentum block 

```math
\Gamma_p = \begin{pmatrix} 2 & -1/2 & -1/2 \\ -1/2 & 2 & -1/2 \\ -1/2 & -1/2 & 2 \end{pmatrix};
```

it is admissible.  
<sub>`Sealed.witness_three_site`</sub>

**32.** On $`V = \mathbb R^2`$ the form $`\sigma(u, w) = u_1 w_2 - u_2 w_1`$ is alternating and nondegenerate, so the simplicity statement applies to it, and its CCR algebra is not the zero algebra.  
<sub>`Sealed.witness_nondegenerate_plane`</sub>

**33.** The vacuum data satisfy the state condition: on $`V = \mathbb R^2`$ with $`\sigma(u, w) = u_1 w_2 - u_2 w_1`$, the form $`\gamma(u, w) = u_1 w_1 + u_2 w_2`$ is symmetric and $`\gamma + i\sigma \ge 0`$ on every finite family of vectors.  
<sub>`Sealed.witness_vacuum_state_condition`</sub>

**34.** The creation operator $`a_j^\dagger`$ raises the particle number.  
<sub>`Sealed.witness_create_raisesParticleNumber`</sub>

**35.** The identity channel: let $`\sigma`$ be any real bilinear form on $`V`$. The data $`L = \mathrm{id}`$, $`\nu = 0`$, $`\mu = 0`$ satisfy the hypotheses that entry 21 places on each channel: $`\nu`$ is symmetric, the channel condition holds (every Gram matrix is $`0`$), and the identity map $`f(a) = a`$ of $`\mathrm{CCR}(V, \sigma)`$ is completely positive with 

```math
f(W(u)) = \exp(i\mu(u) - \nu(u, u)/4)\, W(Lu) = W(u).
```  
<sub>`Sealed.witness_identity_channel`</sub>

**36.** The identity automorphism: let $`\sigma`$ be any real bilinear form on $`V`$. The identity $`\mathbb C`$-linear star automorphism $`T`$ of $`\mathrm{CCR}(V, \sigma)`$, with $`\Gamma = \mathrm{id}`$ and $`c = 1`$, satisfies $`T(W(u)) = c(u)\, W(\Gamma u)`$ for every $`u`$. Together with entry 32 it gives an instance of the hypotheses of entry 18.  
<sub>`Sealed.witness_identity_automorphism`</sub>

## The Gaussian wave function: Schwartz domain, moments and units

A Schwartz function is a smooth function $`\mathbb R \to \mathbb C`$ whose derivatives of every order decay faster than every power of $`|x|`$; it is square integrable, and its class in $`L^2(\mathbb R)`$ carries the $`L^2`$ norm. The Schwartz functions form a common domain for the position $`x\psi`$ and the momentum $`-i\hbar\psi'`$. Throughout this section 

```math
\psi(x) = (\sqrt{\pi}\, s)^{-1/2} e^{-x^2/(2s^2)}
```

is the Gaussian of entry 8, of width $`s > 0`$.

**37.** Let $`s > 0`$ and 

```math
\psi(x) = (\sqrt{\pi}\, s)^{-1/2} e^{-x^2/(2s^2)}.
```

Then $`\psi`$ is a Schwartz function (exactly one Schwartz function equals $`\psi`$ at every point), and its class in $`L^2(\mathbb R)`$ has norm $`1`$.  
<sub>`Sealed.gaussian_schwartz_unique`</sub>

**38.** Moments: let $`s > 0`$, $`\hbar > 0`$ and 

```math
\psi(x) = (\sqrt{\pi}\, s)^{-1/2} e^{-x^2/(2s^2)}.
```

Then $`x\psi`$ and $`-i\hbar\psi'`$ are Schwartz functions, and $`-i\hbar\psi'(x) = (i\hbar/s^2)\, x\psi(x)`$ for every $`x`$. The first moments vanish, 

```math
\int \bar\psi\, x\psi\, dx = 0
```

and 

```math
\int \bar\psi\, (-i\hbar\psi')\, dx = 0,
```

and the second moments are 

```math
\int |x\psi|^2\, dx = s^2/2,
```



```math
\int |{-i\hbar\psi'}|^2\, dx = \hbar^2/(2s^2)
```

and 

```math
\int \overline{x\psi}\, (-i\hbar\psi')\, dx = i\hbar/2.
```  
<sub>`Sealed.gaussian_moments`</sub>

**39.** Dimensionless units: for $`s > 0`$ and $`\hbar > 0`$ let $`D = \mathrm{diag}(1/s, s/\hbar)`$, the rescaling $`q \mapsto q/s`$, $`p \mapsto sp/\hbar`$ of position and momentum. Then 

```math
D\, \mathrm{diag}(s^2, \hbar^2/s^2)\, D^T = 1:
```

in these units the covariance of entry 8 is the vacuum covariance $`1`$.  
<sub>`Sealed.gaussian_dimensionless`</sub>

**40.** The width $`s^2 = \hbar/(m\omega)`$: let $`m > 0`$, $`\omega > 0`$, $`\hbar > 0`$ and $`s = \sqrt{\hbar/(m\omega)}`$. Let $`\psi`$, $`A_q\psi = x\psi`$, $`A_p\psi = -i\hbar\psi'`$ and the matrix $`\gamma`$ be as in entry 8 for this $`s`$. Then $`\gamma = \mathrm{diag}(\hbar/(m\omega), \hbar m\omega)`$.  
<sub>`Sealed.gaussian_oscillator`</sub>

## Fourier analysis, product covariances and Gaussian kernels

A periodic chain is homogeneous when every site carries the same local matrix $`\Gamma`$; its contracted covariance $`\gamma`$ is that of entries 9 and 13 with input matrix of entry 11. The sites are $`x, y \in \{0, \dots, N - 1\}`$, and $`a_x`$ for $`a \in \{q, p\}`$ denotes the position or momentum coordinate of the physical mode of site $`x`$. For $`k \in \{0, \dots, N - 1\}`$ the character of $`\mathbb Z/N`$ is $`\chi_k(x) = e^{-2\pi i k x/N}`$. A complex matrix $`E`$ is positive definite when it is Hermitian with $`\bar z^T E z > 0`$ for every nonzero complex vector $`z`$, and $`H^*`$ is the conjugate transpose of $`H`$.

**41.** The symbols of a homogeneous chain: let $`\Gamma`$ be a real $`2(2M+1) \times 2(2M+1)`$ matrix, regarded as complex, and $`\Gamma_{VV}`$, $`\Gamma_{VC}`$, $`\Gamma_{CC}`$ its blocks on the coordinates of the virtual modes and of the physical mode: the virtual coordinates are listed as the positions and then the momenta of the modes $`A_a`$ (local mode $`a < M`$), followed by the positions and then the momenta of the modes $`B_a`$ (local mode $`M + a`$); the physical coordinates are those of local mode $`2M`$. For $`k`$ let $`\tau`$ be the diagonal $`2M \times 2M`$ matrix with entries $`1`$ on positions and $`-1`$ on momenta, and $`S_k = (1 \mid e^{-2\pi i k/N}\tau)`$ the $`2M \times 4M`$ matrix whose first $`2M`$ columns, those of the coordinates of the modes $`A_a`$, form the identity matrix and whose last $`2M`$ columns, those of the coordinates of the modes $`B_a`$, form $`e^{-2\pi i k/N}\tau`$. The eliminated symbol is $`E_k = S_k \Gamma_{VV} S_k^*`$, and the covariance symbol is the $`2 \times 2`$ complex matrix 

```math
\Sigma_k = \Gamma_{CC} - (S_k\Gamma_{VC})^* E_k^{-1} (S_k\Gamma_{VC}),
```

where $`E_k^{-1}`$ is the matrix inverse.  
<sub>`Sealed.covarianceSymbol_eq`</sub>

**42.** Fourier block diagonalization: let $`N \ge 3`$, $`M \ge 1`$, $`\Gamma`$ admissible on $`2M + 1`$ modes, and $`\gamma`$ the contracted covariance of the homogeneous periodic chain with local matrix $`\Gamma`$ at every site. Then $`\gamma`$ is invariant under the rotation $`x \mapsto x + 1 \bmod N`$ of the sites, 

```math
\gamma(a_{x+1}, b_{y+1}) = \gamma(a_x, b_y)
```

for $`a, b \in \{q, p\}`$; every eliminated symbol $`E_k`$ is positive definite; and the Fourier transform of $`\gamma`$ is block diagonal with the covariance symbols as blocks: 

```math
\frac1N \sum_{x, y} \chi_k(x)\, \gamma(a_x, b_y)\, \overline{\chi_l(y)} = \delta_{kl}\, \Sigma_k(a, b)
```

for all $`k, l`$ and $`a, b \in \{q, p\}`$.  
<sub>`Sealed.fourier_block_diagonal`</sub>

**43.** Fourier reconstruction: under the hypotheses of entry 42, 

```math
\gamma(a_x, b_y) = \frac1N \sum_k \overline{\chi_k(x)}\, \Sigma_k(a, b)\, \chi_k(y)
```

for all sites $`x, y`$ and $`a, b \in \{q, p\}`$; every covariance symbol satisfies $`\Sigma_k - i\Omega \ge 0`$, with $`\Omega`$ the symplectic matrix of one mode; and $`\Sigma_l`$ is the entrywise complex conjugate of $`\Sigma_k`$ whenever $`k + l \equiv 0 \pmod N`$.  
<sub>`Sealed.fourier_reconstruction`</sub>

**44.** Product resources and product covariances: for a real $`2 \times 2`$ matrix $`\theta`$ on one mode, the product resource on $`2M + 1`$ local modes is the independent sum, as in entry 5, of the vacuum $`1`$ on the first $`2M`$ local modes (the virtual modes) and $`\theta`$ on the last local mode (the physical mode). For real $`2 \times 2`$ matrices $`\eta_x`$, one for each site $`x`$ of $`N`$, the product covariance on $`N`$ modes has the entry $`\eta_x(a, b)`$ between the coordinates $`a_x`$ and $`b_x`$ of the same mode and $`0`$ between coordinates of different modes.  
<sub>`Sealed.productCovariance_eq`</sub>

**45.** Product covariances as periodic contractions: let $`N \ge 3`$, $`M \ge 1`$ and let every $`\eta_x`$ be admissible on one mode. Take as input of the periodic chain with $`M`$ virtual modes on each side of every bond (entries 11 to 13) the product resources with physical matrices $`\eta_x`$. Then every product resource is admissible; the matrix $`K\gamma K^T`$, for the wiring $`K`$ and the input $`\gamma`$, is block diagonal with $`2 \cdot 1`$ on the $`2NM`$ eliminated rows and the product covariance $`\eta`$ on the physical rows; the contracted covariance equals $`\eta`$; and $`\eta`$ is admissible.  
<sub>`Sealed.isAdmissible_product`</sub>

**46.** The covariance of a Gaussian kernel: for a complex $`n \times n`$ matrix $`K`$ with real part $`X`$ and imaginary part $`-Y`$, so that $`K = X - iY`$, the kernel covariance is the real $`2n \times 2n`$ matrix 

```math
\begin{pmatrix} X^{-1} & X^{-1}Y \\ YX^{-1} & X + YX^{-1}Y \end{pmatrix}
```

in the blocks of positions and momenta, with $`X^{-1}`$ the matrix inverse.  
<sub>`Sealed.kernelCovariance_eq`</sub>

**47.** The local resource of a finitely squeezed cluster chain: for real $`t`$, $`g`$ and $`g_i`$ let $`r = t/(4(1 + g^2))`$ and $`\alpha = r + i`$. The local resource is the kernel covariance (entry 46) of the three-mode kernel 

```math
\begin{pmatrix} \alpha & 0 & i \\ 0 & \alpha & -2g_i\alpha \\ i & -2g_i\alpha & t - 1/(2\alpha) + 2g_i^2\alpha \end{pmatrix}
```

on the left virtual, the right virtual and the physical mode.  
<sub>`Sealed.clusterLocalResource_eq`</sub>

**48.** Gaussian kernels give admissible covariances: if the complex $`n \times n`$ matrix $`K`$ is symmetric, $`K^T = K`$, and its real part $`X`$ is positive definite ($`x^T X x > 0`$ for every nonzero real vector $`x`$, $`X`$ symmetric), then the kernel covariance of $`K`$ is admissible.  
<sub>`Sealed.isAdmissible_kernelCovariance`</sub>

**49.** Finitely squeezed cluster chains: for $`t > 0`$ and $`g_i \in \{0, g\}`$ the local resource of entry 47 is admissible on three modes.  
<sub>`Sealed.isAdmissible_clusterLocalResource`</sub>

## Weyl systems, relabelling and representations

Let $`\mathcal A`$ be a unital C*-algebra. A Weyl system for $`(V, \sigma)`$ in $`\mathcal A`$ is a map $`W : V \to \mathcal A`$ such that every $`W(u)`$ is unitary, the Weyl relation 

```math
W(u) W(w) = e^{-i\sigma(u, w)/2} W(u + w)
```

holds, and the $`W(u)`$ generate $`\mathcal A`$: the norm closure of the star subalgebra generated by them is $`\mathcal A`$. A representation of a C*-algebra $`\mathcal A`$ on a complex Hilbert space $`H`$ is a $`\mathbb C`$-linear unital star homomorphism $`\pi`$ from $`\mathcal A`$ to the bounded operators on $`H`$.

**50.** Let $`\sigma`$ be alternating and $`W`$ a Weyl system for $`(V, \sigma)`$ in a unital C*-algebra $`\mathcal A`$. Then $`W(0) = 1`$, $`W(u)^* = W(-u)`$, 

```math
W(u) W(w) = e^{-i\sigma(u, w)} W(w) W(u)
```

for all $`u, w`$, and $`W(u)`$ and $`W(w)`$ commute whenever $`\sigma(u, w) = 0`$.  
<sub>`Sealed.weylSystem_relations`</sub>

**51.** The CCR algebra is a Weyl system: for alternating $`\sigma`$ the Weyl operators $`W(u)`$, as elements of $`\mathrm{CCR}(V, \sigma)`$, form a Weyl system for $`(V, \sigma)`$ in $`\mathrm{CCR}(V, \sigma)`$.  
<sub>`Sealed.weylSystem_CCR`</sub>

**52.** Pullback of a Weyl system: let $`\sigma`$ and $`\sigma_0`$ be real bilinear forms on $`V`$ and $`V_0`$, $`W`$ a Weyl system for $`(V_0, \sigma_0)`$ in a unital C*-algebra $`\mathcal A`$, and $`T : V \to V_0`$ a linear map with $`\sigma_0(Tu, Tw) = \sigma(u, w)`$. Then every $`W(Tu)`$ is unitary and $`u \mapsto W(Tu)`$ satisfies the Weyl relation of $`\sigma`$; if $`T`$ is surjective, the $`W(Tu)`$ generate $`\mathcal A`$, so that $`u \mapsto W(Tu)`$ is a Weyl system for $`(V, \sigma)`$.  
<sub>`Sealed.weylSystem_pullback`</sub>

**53.** The relabelling maps: let $`\sigma`$ and $`\sigma'`$ be real bilinear forms on $`V`$ and $`V'`$, and $`T : V \to V'`$ a linear bijection with $`\sigma'(Tu, Tv) = \sigma(u, v)`$. The relabelling unitary $`U_T`$, a linear isometric bijection $`\ell^2(V) \to \ell^2(V')`$, is $`(U_T f)(v') = f(T^{-1}v')`$, and the relabelling $`\alpha_T`$, a $`\mathbb C`$-linear star isomorphism $`\mathrm{CCR}(V, \sigma) \to \mathrm{CCR}(V', \sigma')`$, is $`\alpha_T(a) = U_T\, a\, U_T^{-1}`$.  
<sub>`Sealed.relabel_eq`</sub>

**54.** Relabelling is functorial: let $`\sigma`$, $`\sigma'`$, $`\sigma''`$ be real bilinear forms on $`V`$, $`V'`$, $`V''`$, and $`T_1 : V \to V'`$, $`T_2 : V' \to V''`$ linear bijections with $`\sigma'(T_1u, T_1v) = \sigma(u, v)`$ and 

```math
\sigma''(T_2u', T_2v') = \sigma'(u', v').
```

Then $`\alpha_{T_1}(W(u)) = W'(T_1u)`$ for every $`u \in V`$, the relabelling by the identity of $`V`$ is the identity of $`\mathrm{CCR}(V, \sigma)`$, and 

```math
\alpha_{T_2 T_1} = \alpha_{T_2} \circ \alpha_{T_1}.
```  
<sub>`Sealed.relabel_functorial`</sub>

**55.** Injectivity of representations: let $`\sigma`$ be alternating and nondegenerate. Every representation of $`\mathrm{CCR}(V, \sigma)`$ on a nonzero complex Hilbert space is injective.  
<sub>`Sealed.injective_representation`</sub>

## States and the state condition

States and characteristic functions are as in the section on states and Gaussian states.

**56.** Twisted positivity: let $`\sigma`$ be alternating, $`\omega`$ a state on $`\mathrm{CCR}(V, \sigma)`$ and $`\chi(u) = \omega(W(u))`$ its characteristic function. For every finite family $`u_1, \dots, u_m`$ of vectors the twisted kernel $`\big(e^{i\sigma(u_j, u_k)/2}\, \chi(u_k - u_j)\big)_{jk}`$ is positive semidefinite.  
<sub>`Sealed.twistedKernel_posSemidef`</sub>

**57.** The norm bound: let $`\sigma`$ be any real bilinear form on $`V`$ and $`\omega`$ a state on $`\mathrm{CCR}(V, \sigma)`$. Then $`|\omega(a)| \le \|a\|`$ for every $`a`$.  
<sub>`Sealed.norm_state_le`</sub>

**58.** The three forms of the state condition: let $`\gamma`$ be a symmetric and $`\sigma`$ an alternating real bilinear form on $`V`$. The conditions (a) $`\gamma + i\sigma \ge 0`$, that is, the complex matrix $`(\gamma(u_j, u_k) + i\sigma(u_j, u_k))_{jk}`$ is positive semidefinite for every finite family $`u_1, \dots, u_m`$; (b) $`2\sigma(a, b) \le \gamma(a, a) + \gamma(b, b)`$ for all $`a, b`$; and (c) $`\gamma(u, u) \ge 0`$ and $`\sigma(u, w)^2 \le \gamma(u, u)\gamma(w, w)`$ for all $`u, w`$, are equivalent: (a) holds if and only if (b) holds, and (b) if and only if (c).  
<sub>`Sealed.state_condition_iff`</sub>

## Gaussian channels: product formula, special cases and dilations

Gaussian channels $`(L, \nu, \mu, f)`$ are as in the section on Gaussian channels; their dissipation form is 

```math
C(u, w) = \nu(u, w) + i\sigma(u, w) - i\sigma(Lu, Lw).
```

A C*-algebra with a partial order is star-ordered when $`a \le b`$ holds exactly if $`b = a + p`$ for a finite sum $`p`$ of elements of the form $`s^* s`$.

**59.** The product formula: let $`\sigma`$ be alternating and $`(L, \nu, \mu, f)`$ a Gaussian channel on $`\mathrm{CCR}(V, \sigma)`$. Then 

```math
f(W(u) W(w)) = e^{-C(u, w)/2}\, f(W(u))\, f(W(w))
```

for all $`u, w \in V`$.  
<sub>`Sealed.gaussianChannel_product`</sub>

**60.** Channels and Gaussian states: let $`\sigma`$ be any real bilinear form on $`V`$, $`(L, \nu, \mu, f)`$ a Gaussian channel on $`\mathrm{CCR}(V, \sigma)`$, and $`\omega`$ a given state that is Gaussian with symmetric covariance form $`\gamma`$ and linear displacement $`d`$, that is 

```math
\omega(W(u)) = \exp(i d(u) - \gamma(u, u)/4).
```

Then $`\omega'(a) = \omega(f(a))`$ defines a state $`\omega'`$, and $`\omega'`$ is Gaussian with the symmetric covariance form $`\gamma(L\cdot, L\cdot) + \nu`$ and the displacement $`d \circ L + \mu`$: 

```math
\omega'(W(u)) = \exp(i (d(Lu) + \mu(u)) - (\gamma(Lu, Lu) + \nu(u, u))/4).
```

The statement assumes the Gaussian state $`\omega`$; the library constructs no Gaussian state, and the existence of Gaussian states is a candidate for a later theorem, as in entry 20. Apart from states obtained from given ones, as here, the only state constructed is the vector state of entry 67, which is not Gaussian for $`V \ne 0`$, since its characteristic function vanishes away from $`0`$.  
<sub>`Sealed.gaussianChannel_state`</sub>

**61.** No noise: let $`\sigma`$ be alternating and $`L : V \to V`$ a linear map such that the data $`(L, 0)`$ satisfy the channel condition, that is, the complex matrix $`(i\sigma(u_j, u_k) - i\sigma(Lu_j, Lu_k))_{jk}`$ is positive semidefinite for every finite family $`u_1, \dots, u_m`$. Then $`L`$ preserves $`\sigma`$: $`\sigma(Lu, Lw) = \sigma(u, w)`$.  
<sub>`Sealed.noiseless_preserves`</sub>

**62.** The noiseless channel as a relabelling: let $`\sigma`$ be alternating and $`L : V \to V`$ a linear bijection with $`\sigma(Lu, Lv) = \sigma(u, v)`$. The relabelling $`\alpha_L`$ of entry 53 is completely positive, and every completely positive map $`f`$ of $`\mathrm{CCR}(V, \sigma)`$ with $`f(W(u)) = W(Lu)`$ for every $`u`$, that is, every Gaussian channel with data $`(L, 0, 0)`$, equals $`\alpha_L`$.  
<sub>`Sealed.noiseless_channel_relabel`</sub>

**63.** Dilations at the level of covariances: let $`\sigma`$ and $`\sigma'`$ be real bilinear forms on $`V`$ (the system) and $`V'`$ (the ancilla), and $`S : V \times V' \to V \times V'`$ a linear map preserving $`\sigma \oplus \sigma'`$: 

```math
\sigma(S(x)_1, S(y)_1) + \sigma'(S(x)_2, S(y)_2) = \sigma(x_1, y_1) + \sigma'(x_2, y_2).
```

Write $`Au = S(u, 0)_1`$ and $`Cu = S(u, 0)_2`$, and let $`\gamma`$, $`\gamma'`$ be real bilinear forms on $`V`$, $`V'`$. Then (i) 

```math
\sigma(Au, Aw) + \sigma'(Cu, Cw) = \sigma(u, w);
```

(ii) if $`\gamma' + i\sigma' \ge 0`$ on every finite family, the data $`(A, \gamma'(C\cdot, C\cdot))`$ satisfy the channel condition 

```math
\gamma'(C\cdot, C\cdot) + i\sigma - i\sigma(A\cdot, A\cdot) \ge 0
```

on every finite family; (iii) the reduced covariance is 

```math
(\gamma \oplus \gamma')(S(u, 0), S(w, 0)) = \gamma(Au, Aw) + \gamma'(Cu, Cw),
```

as an identity of bilinear forms.  
<sub>`Sealed.dilation_identities`</sub>

**64.** Closed star subalgebras are star-ordered: let $`\mathcal A`$ be a unital C*-algebra with a partial order for which it is star-ordered, and $`\mathcal S`$ a norm-closed unital star subalgebra of $`\mathcal A`$ with the order inherited from $`\mathcal A`$. Then an element $`x`$ of $`\mathcal S`$ satisfies $`x \ge 0`$ if and only if $`x = s^* s`$ for some $`s \in \mathcal S`$, and $`\mathcal S`$ is star-ordered.  
<sub>`Sealed.starOrdered_of_isClosed`</sub>

**65.** Completely positive maps compose: let $`\mathcal A`$, $`\mathcal B`$, $`\mathcal C`$ be unital C*-algebras, each with a partial order for which it is star-ordered, and $`f : \mathcal A \to \mathcal B`$ and $`g : \mathcal B \to \mathcal C`$ completely positive maps. Then $`a \mapsto g(f(a))`$ is completely positive, and so is the identity of $`\mathcal A`$.  
<sub>`Sealed.cp_comp`</sub>

## Further examples

These examples show that the hypotheses of entries 55, 56 and 57 can be met.

**66.** A representation: let $`\sigma`$ be any real bilinear form on $`V`$. The Hilbert space $`\ell^2(V)`$ is nonzero, and the inclusion of $`\mathrm{CCR}(V, \sigma)`$ in the bounded operators on $`\ell^2(V)`$ is a representation. With entry 32 it gives an instance of the hypotheses of entry 55.  
<sub>`Sealed.witness_inclusion_representation`</sub>

**67.** A state: let $`\sigma`$ be alternating. There is a state $`\omega`$ on $`\mathrm{CCR}(V, \sigma)`$ with characteristic function $`\omega(W(u)) = 1`$ for $`u = 0`$ and $`\omega(W(u)) = 0`$ for $`u \ne 0`$ (the vector state $`a \mapsto \langle \delta_0, a\, \delta_0 \rangle`$ of the basis vector at $`0`$).  
<sub>`Sealed.witness_vector_state`</sub>

## The formal Fock space of one mode

For one mode the set of modes $`\iota`$ has one element, and $`a`$, $`a^\dagger`$ are the annihilation and creation operators of entry 23 on the formal Fock space with complex coefficients.

**68.** Anti-normal ordering and the number operator: the monomials $`a^m (a^\dagger)^k`$ with $`m, k \in \mathbb N`$, in which every annihilation operator stands to the left of every creation operator, span the algebra generated by $`a`$ and $`a^\dagger`$ as a complex vector space of linear maps of the formal Fock space; and the number operator $`\hat n = a^\dagger a`$ satisfies 

```math
\hat n^2 = a^2 (a^\dagger)^2 - 3\, a a^\dagger + 1.
```  
<sub>`Sealed.antinormal_span_and_number_sq`</sub>

## The bosonic Fock space

The bosonic Fock space $`\Gamma_s(\iota)`$ of the modes $`\iota`$ is the Hilbert space $`\ell^2`$ of the occupation-number configurations $`n`$, with the inner product 

```math
\langle\varphi, \psi\rangle = \sum_n \overline{\varphi(n)}\, \psi(n);
```

the number state $`|m\rangle`$ is the basis vector at $`m`$, and the vacuum $`|0\rangle`$ is the basis vector at the configuration $`0`$. The embedding $`\jmath`$ sends $`\psi \in \Gamma_s(\iota)`$ to the formal vector with the same coefficients. A linear map $`T`$ of the formal Fock space $`\mathcal F(\iota, \mathbb C)`$ is coefficient-finite when for every $`n`$ there is a finite set $`s`$ of configurations such that $`(T\varphi)(n) = (T\varphi')(n)`$ whenever $`\varphi(m) = \varphi'(m)`$ for all $`m \in s`$.

**69.** The Fock space and the embedding: (definition) $`\Gamma_s(\iota)`$ is $`\ell^2`$ of the configurations, and the embedding keeps the coefficients, $`(\jmath\psi)(n) = \psi(n)`$. The embedding is injective, and a formal vector $`\varphi`$ lies in its image if and only if $`\sum_n |\varphi(n)|^2 < \infty`$. (Definition) The squared norm of a formal vector is 

```math
\|\varphi\|^2 = \sum_n |\varphi(n)|^2 \in [0, \infty].
```

Moreover $`\|\jmath\psi\|^2`$ is the squared Hilbert norm of $`\psi`$, and the number states span a dense subspace of $`\Gamma_s(\iota)`$.  
<sub>`Sealed.fockSpace_eq`</sub>

**70.** Maximal realizations: (definition) for a linear map $`T`$ of $`\mathcal F(\iota, \mathbb C)`$, the maximal realization $`\bar T`$ is the operator of $`\Gamma_s(\iota)`$ with the domain of the $`\psi`$ for which $`T\jmath\psi`$ is square-summable, and with $`\jmath \bar T\psi = T\jmath\psi`$. If $`T`$ is coefficient-finite, then $`\bar T`$ is closed: its graph is closed in $`\Gamma_s(\iota) \times \Gamma_s(\iota)`$.  
<sub>`Sealed.maxRealization_isClosed`</sub>

**71.** Closed forms: let $`T_k`$, $`k`$ in a finite index set, be coefficient-finite linear maps of $`\mathcal F(\iota, \mathbb C)`$, and let $`\psi_r \to \psi`$ in $`\Gamma_s(\iota)`$ with every $`T_k\jmath\psi_r`$ square-summable and $`\sum_k \|T_k\jmath(\psi_r - \psi_s)\|^2 \to 0`$ as $`r, s \to \infty`$. Then every $`T_k\jmath\psi`$ is square-summable and $`\sum_k \|T_k\jmath(\psi_r - \psi)\|^2 \to 0`$: the form with the diagonal $`\sum_k \|\bar T_k\psi\|^2`$ on the intersection of the domains of the $`\bar T_k`$ is closed.  
<sub>`Sealed.form_closed`</sub>

## Second quantization

The set of modes $`\iota`$ is finite, and matrices are indexed by the modes. A complex matrix $`\mathcal U`$ is unitary when $`\mathcal U^* \mathcal U = \mathcal U \mathcal U^* = 1`$, and the exponential of a matrix is 

```math
e^h = \sum_{k \ge 0} h^k / k!.
```

**72.** Second quantization (definition): for a complex matrix $`g`$, $`\Gamma(g)`$ is the linear map of $`\mathcal F(\iota, \mathbb C)`$ that becomes, under the Bargmann map of entry 27, the substitution of the linear forms 

```math
(g^T z)_j = \sum_k g_{kj} z_k
```

for the variables: $`\mathfrak B\, \Gamma(g)\psi = (\mathfrak B\psi)(g^T z)`$. Since $`\mathfrak B`$ is a bijection, this determines $`\Gamma(g)`$.  
<sub>`Sealed.secondQuant_eq`</sub>

**73.** Representation and intertwining: $`\Gamma(1) = 1`$ and $`\Gamma(g g') = \Gamma(g)\Gamma(g')`$ for all complex matrices $`g`$, $`g'`$, and on the whole formal Fock space 

```math
\Gamma(g)\, a_j^\dagger = \big(\sum_k g_{kj} a_k^\dagger\big)\Gamma(g)
```

and 

```math
a_j\, \Gamma(g) = \Gamma(g) \sum_k g_{jk} a_k.
```  
<sub>`Sealed.secondQuant_representation`</sub>

**74.** Unitarity and strong continuity: for a unitary matrix $`\mathcal U`$, $`\|\Gamma(\mathcal U)\varphi\|^2 = \|\varphi\|^2`$ in $`[0, \infty]`$ for every formal vector $`\varphi`$, and on the whole formal Fock space 

```math
\Gamma(\mathcal U^*)\, a_j\, \Gamma(\mathcal U) = \sum_k \mathcal U_{jk} a_k.
```

(Definition) The unitary operator $`\mathsf U_{\mathcal U}`$ of $`\Gamma_s(\iota)`$ is the restriction of $`\Gamma(\mathcal U)`$: $`\jmath\, \mathsf U_{\mathcal U}\psi = \Gamma(\mathcal U)\jmath\psi`$. The map $`\mathcal U \mapsto \mathsf U_{\mathcal U}`$ is a group homomorphism from the unitary matrices to the unitary operators of $`\Gamma_s(\iota)`$, with $`\mathsf U_{\mathcal U}^* = \mathsf U_{\mathcal U^*}`$, and $`\mathcal U \mapsto \mathsf U_{\mathcal U}\psi`$ is continuous for every $`\psi \in \Gamma_s(\iota)`$.  
<sub>`Sealed.secondQuant_unitary`</sub>

**75.** The exponential form: (definition) for a complex matrix $`h`$ let 

```math
\mathrm d\Gamma(h) = \sum_{j, k} h_{jk}\, a_j^\dagger a_k.
```

For every formal vector $`\psi`$ and every $`n`$ the series 

```math
\sum_{r \ge 0} (\mathrm d\Gamma(h)^r\psi)(n)/r!
```

converges, with sum $`(\Gamma(e^h)\psi)(n)`$: $`\Gamma(e^h) = e^{\mathrm d\Gamma(h)}`$, the exponential taken coefficientwise.  
<sub>`Sealed.secondQuant_exp`</sub>

**76.** Unitary matrices are exponentials: every unitary matrix is $`e^{iM}`$ for a Hermitian matrix $`M`$, and $`e^{iM}`$ is unitary for every Hermitian $`M`$. So entry 75 applies to every $`\Gamma(\mathcal U)`$, with $`h = iM`$.  
<sub>`Sealed.unitary_eq_exp`</sub>

## Symplectic matrices: the Bloch–Messiah decomposition

A real $`2n \times 2n`$ matrix $`S`$, indexed by positions and momenta as in the first section, is symplectic when $`S \Omega S^T = \Omega`$, and orthogonal when $`S^T S = 1`$. A real matrix $`P`$ is symmetric positive definite when $`P^T = P`$ and $`x^T P x > 0`$ for every nonzero real vector $`x`$. A vector $`r \in \mathbb R^n`$ satisfies $`r \ge 0`$ when $`r_k \ge 0`$ for every $`k`$.

**77.** The squeezing matrix and the orthogonal symplectic matrix of a unitary (definitions): for $`r \in \mathbb R^n`$, 

```math
\Sigma(r) = \mathrm{diag}(e^{-r_1}, \dots, e^{-r_n}, e^{r_1}, \dots, e^{r_n});
```

for a unitary $`n \times n`$ matrix $`\mathcal U = X + iY`$ with $`X`$, $`Y`$ real, 

```math
O_{\mathcal U} = \begin{pmatrix} X & -Y \\ Y & X \end{pmatrix}.
```

Both are symplectic, and $`O_{\mathcal U}`$ is orthogonal.  
<sub>`Sealed.squeezingMatrix_eq`</sub>

**78.** Orthogonal symplectic matrices and unitaries: a real $`2n \times 2n`$ matrix $`O`$ is orthogonal and symplectic if and only if $`O = O_{\mathcal U}`$ for a unitary $`\mathcal U`$; and $`O_{\mathcal U \mathcal V} = O_{\mathcal U} O_{\mathcal V}`$, $`O_1 = 1`$, $`O_{\mathcal U^*} = O_{\mathcal U}^T`$.  
<sub>`Sealed.orthogonalSymplectic_iff`</sub>

**79.** The Bloch–Messiah decomposition: for every symmetric positive definite symplectic matrix $`M`$ there are a unitary $`\mathcal U`$ and $`r \ge 0`$ with $`M = O_{\mathcal U} \Sigma(r)^2 O_{\mathcal U}^T`$; for every symplectic matrix $`S`$ there are unitaries $`\mathcal U`$, $`\mathcal V`$ and $`r \ge 0`$ with $`S = O_{\mathcal U} \Sigma(r) O_{\mathcal V}`$.  
<sub>`Sealed.blochMessiah`</sub>

**80.** The squeezing parameters are unique up to order: if $`O_1 \Sigma(r) O_2 = O_3 \Sigma(r') O_4`$ with orthogonal $`O_1, \dots, O_4`$ and $`r, r' \ge 0`$, then $`r' = r \circ \pi`$ for a permutation $`\pi`$ of $`\{1, \dots, n\}`$.  
<sub>`Sealed.blochMessiah_squeezing_unique`</sub>

**81.** The polar decomposition: for symplectic $`S`$, the positive semidefinite square root $`P = (S S^T)^{1/2}`$ is symmetric positive definite and symplectic, $`P^{-1} S`$ is orthogonal and symplectic, and $`S = P\, (P^{-1} S)`$. For every real $`2n \times 2n`$ matrix $`S`$, if $`S = P' O'`$ with $`P'`$ symmetric positive definite and $`O'`$ orthogonal, then $`P' = (S S^T)^{1/2}`$ and $`O' = P'^{-1} S`$.  
<sub>`Sealed.polar_decomposition_symplectic`</sub>

## Exponential vectors, displacement and squeezing

The set of modes $`\iota`$ is finite. For $`w, z \in \mathbb C^\iota`$, $`\langle w, z\rangle`$ denotes $`\sum_j \bar w_j z_j`$ and $`|z|^2`$ denotes $`\sum_j |z_j|^2`$; for a configuration $`m`$, $`z^m`$ denotes $`\prod_j z_j^{m_j}`$ and $`m!`$ denotes $`\prod_j m_j!`$. Operators are bounded operators of $`\Gamma_s(\iota)`$, with the adjoint as star; $`|0\rangle`$ is the vacuum.

**82.** Exponential vectors: (definition) for $`z \in \mathbb C^\iota`$ the exponential vector $`\varepsilon(z) \in \Gamma_s(\iota)`$ has the coefficients 

```math
\varepsilon(z)(m) = z^m/\sqrt{m!};
```

and $`\langle \varepsilon(w), \varepsilon(z)\rangle = e^{\langle w, z\rangle}`$.  
<sub>`Sealed.expVec_apply`</sub>

**83.** Totality: the exponential vectors span a dense subspace of $`\Gamma_s(\iota)`$. Hence a vector $`\psi`$ is determined by the inner products $`\langle \varepsilon(w), \psi\rangle`$, $`w \in \mathbb C^\iota`$, and a continuous linear map from $`\Gamma_s(\iota)`$ to a Hausdorff topological vector space is determined by its values on the exponential vectors.  
<sub>`Sealed.totality`</sub>

**84.** Displacement operators: for $`\alpha \in \mathbb C^\iota`$, $`D(\alpha)`$ is a unitary operator of $`\Gamma_s(\iota)`$ with 

```math
D(\alpha)\varepsilon(z) = e^{-|\alpha|^2/2 - \langle\alpha, z\rangle} \varepsilon(z + \alpha)
```

for every $`z`$, which determines it by entry 83; this is the normal-ordered form of $`\exp\big(\sum_j (\alpha_j a_j^\dagger - \bar\alpha_j a_j)\big)`$ (an identification that is not part of the statement). Moreover $`D(\alpha)^* = D(-\alpha)`$, $`D(0) = 1`$, and $`D(\alpha)|0\rangle = e^{-|\alpha|^2/2} \varepsilon(\alpha)`$, the coherent state.  
<sub>`Sealed.displacement_expVec`</sub>

**85.** The Weyl relation and strong continuity: 

```math
D(\alpha) D(\beta) = \exp\big(\frac12 \sum_j (\alpha_j \bar\beta_j - \bar\alpha_j \beta_j)\big) D(\alpha + \beta);
```

along a ray the displacements form a one-parameter group, $`D(t\alpha) D(s\alpha) = D((t + s)\alpha)`$ for real $`t`$, $`s`$; and $`\alpha \mapsto D(\alpha)\psi`$ is continuous for every $`\psi`$.  
<sub>`Sealed.displacement_mul`</sub>

**86.** Displacement of the ladder operators: let $`\psi, \varphi \in \Gamma_s(\iota)`$. If $`a_j\jmath\psi = \jmath\varphi`$, then 

```math
a_j \jmath D(\alpha)\psi = \jmath D(\alpha)\varphi + \alpha_j\, \jmath D(\alpha)\psi;
```

if $`a_j^\dagger\jmath\psi = \jmath\varphi`$, then 

```math
a_j^\dagger \jmath D(\alpha)\psi = \jmath D(\alpha)\varphi + \bar\alpha_j\, \jmath D(\alpha)\psi;
```

and $`D(\alpha)\psi`$ lies in the domain of the maximal realization of $`a_j`$ if and only if $`\psi`$ does. So $`D(\alpha)^* a_j D(\alpha) = a_j + \alpha_j`$ and 

```math
D(\alpha)^* a_j^\dagger D(\alpha) = a_j^\dagger + \bar\alpha_j
```

on these vectors.  
<sub>`Sealed.displacement_ladder`</sub>

**87.** Irreducibility: a bounded operator $`T`$ of $`\Gamma_s(\iota)`$ that commutes with every $`D(\alpha)`$ is $`T = \langle 0|T|0\rangle\, 1`$, and a closed subspace that every $`D(\alpha)`$ maps into itself is $`0`$ or $`\Gamma_s(\iota)`$.  
<sub>`Sealed.displacement_irreducible`</sub>

**88.** Squeezing operators: (definition) for $`\zeta \in \mathbb C`$ let $`\tau(\zeta) = \zeta \tanh|\zeta| / |\zeta|`$, with $`\tau(0) = 0`$. For $`\zeta \in \mathbb C^\iota`$ write $`c_j = \cosh|\zeta_j|`$ and $`\tau_j = \tau(\zeta_j)`$. The squeezing operator $`\mathsf S(\zeta)`$ is a unitary operator of $`\Gamma_s(\iota)`$ with 

```math
\langle \varepsilon(w), \mathsf S(\zeta)\varepsilon(z)\rangle = (\prod_j c_j)^{-1/2} \exp\big(\sum_j \bar\tau_j z_j^2/2\big) \exp\big(\sum_j (-\tau_j \bar w_j^2/2 + z_j \bar w_j / c_j)\big)
```

for all $`w`$, $`z`$, which determines it by entry 83. This is the normal-ordered form of the product $`\prod_j \exp\big(\frac12 (\bar\zeta_j a_j^2 - \zeta_j a_j^{\dagger 2})\big)`$ of one-mode squeezers (an identification that is not part of the statement); for real $`\zeta_j = r_j > 0`$ it squeezes $`\hat q_j`$ (entries 93 and 105). Moreover $`\mathsf S(\zeta)^* = \mathsf S(-\zeta)`$ and $`\mathsf S(0) = 1`$.  
<sub>`Sealed.squeeze_inner_expVec`</sub>

**89.** Squeezing and displacements: 

```math
\mathsf S(\zeta) D(\beta) = D(L_\zeta\beta)\, \mathsf S(\zeta)
```

for every $`\beta`$, with 

```math
(L_\zeta\beta)_j = \cosh|\zeta_j|\, \beta_j - e^{i\phi_j} \sinh|\zeta_j|\, \bar\beta_j,
```

where $`e^{i\phi_j} = \zeta_j/|\zeta_j|`$ (read as $`0`$ when $`\zeta_j = 0`$). Along a ray the squeezing operators form a one-parameter group, 

```math
\mathsf S(t\zeta) \mathsf S(s\zeta) = \mathsf S((t + s)\zeta)
```

for real $`t`$, $`s`$, and $`\zeta \mapsto \mathsf S(\zeta)\psi`$ is continuous for every $`\psi`$.  
<sub>`Sealed.squeeze_mul_displacement`</sub>

## Gaussian unitaries

There are $`n`$ modes, and $`\Gamma_s(n)`$ is the Fock space of the modes $`\{1, \dots, n\}`$. A phase-space vector $`u = (q, p) \in \mathbb R^{2n}`$ is indexed as in the first section, and $`\sigma(u, v) = u^T \Omega v`$. The quadratures $`\hat q_j`$ and $`\hat p_j`$ are the linear maps $`(a_j + a_j^\dagger)/\sqrt2`$ and $`i(a_j^\dagger - a_j)/\sqrt2`$ of the formal Fock space, and $`\hat R = (\hat q, \hat p)`$.

**90.** Weyl operators on Fock space: (definition) for $`u = (q, p)`$, $`W(u) = D(\alpha(u))`$ with 

```math
\alpha(u)_j = (q_j + i p_j)/\sqrt2;
```

formally 

```math
W(u) = \exp(i(p \cdot \hat q - q \cdot \hat p)),
```

an identification that is not part of the statement. They satisfy the Weyl relation 

```math
W(u) W(v) = e^{-i\sigma(u, v)/2} W(u + v),
```

$`W(u)^* = W(-u)`$, and $`\langle 0|W(u)|0\rangle = e^{-|u|^2/4}`$.  
<sub>`Sealed.weylOp_eq`</sub>

**91.** Gaussian unitaries (definition): a unitary operator $`U`$ of $`\Gamma_s(n)`$ is Gaussian with symplectic matrix $`M`$ and displacement vector $`d \in \mathbb R^{2n}`$, or with data $`(M, d)`$, when $`M`$ is symplectic and 

```math
U^* W(u) U = e^{-i\sigma(u, d)} W(M^{-1}u)
```

for every $`u \in \mathbb R^{2n}`$, the exponentiated form of $`U^* \hat R U = M \hat R + d`$ (entry 95).  
<sub>`Sealed.isGaussianUnitary_iff`</sub>

**92.** Composition, adjoint and uniqueness: if $`U_1`$, $`U_2`$ are Gaussian with data $`(M_1, d_1)`$, $`(M_2, d_2)`$, then $`U_1 U_2`$ is Gaussian with data $`(M_1 M_2, d_1 + M_1 d_2)`$; if $`U`$ is Gaussian with data $`(M, d)`$, then $`U^*`$ is Gaussian with data $`(M^{-1}, -M^{-1} d)`$; the data of a Gaussian unitary are unique; and two Gaussian unitaries with the same data differ by a factor $`\lambda`$ with $`|\lambda| = 1`$.  
<sub>`Sealed.isGaussianUnitary_mul`</sub>

**93.** Examples and existence: $`D(\alpha)`$ is Gaussian with data $`(1, \delta(\alpha))`$, where 

```math
\delta(\alpha) = \sqrt2\, (\mathrm{Re}\, \alpha, \mathrm{Im}\, \alpha);
```

$`\mathsf U_{\mathcal U}`$ is Gaussian with data $`(O_{\mathcal U}, 0)`$ for every unitary $`\mathcal U`$; $`\mathsf S(r)`$ with real squeezing parameters $`r \in \mathbb R^n`$ is Gaussian with data $`(\Sigma(r), 0)`$; and for every symplectic $`M`$ and every $`d \in \mathbb R^{2n}`$ there is a Gaussian unitary with data $`(M, d)`$.  
<sub>`Sealed.isGaussianUnitary_examples`</sub>

**94.** Factorization, Proposition 5 of Tjoa and Cirac, arXiv:2607.28753: let $`U`$ be Gaussian with data $`(M, d)`$. If $`M = O_{\mathcal U} \Sigma(r) O_{\mathcal V}`$ with unitaries $`\mathcal U`$, $`\mathcal V`$ and $`r \in \mathbb R^n`$, then 

```math
U = \lambda\, \mathsf U_{\mathcal U} D(\alpha) \mathsf S(r) \mathsf U_{\mathcal V}
```

with $`|\lambda| = 1`$ and $`\alpha = \alpha(O_{\mathcal U}^T d)`$, the complex vector of $`O_{\mathcal U}^T d`$ as for the Weyl operators. Such a decomposition of $`M`$ exists with $`r \ge 0`$: there are unitaries $`\mathcal U`$, $`\mathcal V`$, $`r \ge 0`$ and $`\lambda`$ with $`|\lambda| = 1`$ such that $`M = O_{\mathcal U} \Sigma(r) O_{\mathcal V}`$ and 

```math
U = \lambda\, \mathsf U_{\mathcal U} D(\alpha(O_{\mathcal U}^T d)) \mathsf S(r) \mathsf U_{\mathcal V}.
```  
<sub>`Sealed.gaussianUnitary_factorization`</sub>

**95.** Action on the quadratures: (definition) the quadratures $`\hat q_j`$ and $`\hat p_j`$ are $`(a_j + a_j^\dagger)/\sqrt2`$ and $`i(a_j^\dagger - a_j)/\sqrt2`$. Let $`U`$ be Gaussian with data $`(M, d)`$, and let $`\mathcal Q`$ be the set of $`\psi \in \Gamma_s(n)`$ in the domain of the maximal realization of every $`a_j`$. Then $`U\psi \in \mathcal Q`$ if and only if $`\psi \in \mathcal Q`$. For $`\psi \in \mathcal Q`$ and every phase-space index $`k`$ there is $`\xi \in \Gamma_s(n)`$ with 

```math
\jmath\xi = \sum_l M_{kl} \hat R_l \jmath\psi + d_k \jmath\psi,
```

and for every such $`\xi`$, $`\hat R_k \jmath U\psi = \jmath U\xi`$: 

```math
U^* \hat R_k U = \sum_l M_{kl} \hat R_l + d_k
```

on $`\mathcal Q`$.  
<sub>`Sealed.gaussianUnitary_quadratures`</sub>

## Pure Gaussian states

The characteristic function of $`\psi \in \Gamma_s(n)`$ is $`\chi_\psi(u) = \langle \psi, W(u)\psi\rangle`$, $`u \in \mathbb R^{2n}`$. A pure Gaussian state is a vector $`U|0\rangle`$ with $`U`$ a Gaussian unitary. The covariance matrix $`\gamma`$ is normalized as twice the symmetrized covariance, 

```math
\gamma_{kl} = \langle \{\hat R_k - d_k, \hat R_l - d_l\}\rangle,
```

so that the vacuum has $`\gamma = 1`$ (entry 103); the matrix $`\Gamma`$ of Eq. (13) of Tjoa and Cirac is $`\gamma/2`$.

**96.** A vector is determined up to a phase by its characteristic function: if $`\psi \ne 0`$ and $`\chi_\varphi = \chi_\psi`$, then $`\varphi = \lambda\psi`$ with $`|\lambda| = 1`$. If $`U`$ is Gaussian with data $`(M, d)`$, then 

```math
\chi_{U\psi}(u) = e^{-i\sigma(u, d)} \chi_\psi(M^{-1}u).
```  
<sub>`Sealed.charFun_determines`</sub>

**97.** Gaussian characteristic functions (definition): $`\psi \in \Gamma_s(n)`$ has the Gaussian characteristic function with displacement vector $`d \in \mathbb R^{2n}`$ and covariance matrix $`\gamma`$ when $`\gamma^T = \gamma`$ and 

```math
\chi_\psi(u) = \exp\big(-i\sigma(u, d) - \frac14 u^T \Omega \gamma \Omega^T u\big)
```

for every $`u`$.  
<sub>`Sealed.hasGaussianCharFun_iff`</sub>

**98.** Properties of Gaussian characteristic functions: if $`\psi`$ has the Gaussian characteristic function with $`(d, \gamma)`$, then $`\|\psi\| = 1`$; the data $`(d, \gamma)`$ are unique; $`\gamma`$ is admissible; $`\gamma`$ is symplectic, $`\gamma \Omega \gamma^T = \Omega`$; and every $`\varphi`$ with the Gaussian characteristic function with the same $`(d, \gamma)`$ is $`\varphi = \lambda\psi`$ with $`|\lambda| = 1`$.  
<sub>`Sealed.hasGaussianCharFun_props`</sub>

**99.** Gaussian unitaries on the vacuum: if $`U`$ is Gaussian with data $`(M, d)`$, then $`U|0\rangle`$ has the Gaussian characteristic function with displacement vector $`d`$ and covariance matrix $`M M^T`$. Its moments, Eq. (13) of Tjoa and Cirac: there are $`\phi_k \in \Gamma_s(n)`$, one for each phase-space index $`k`$, with $`\hat R_k \jmath U|0\rangle = \jmath\phi_k`$, $`\langle U|0\rangle, \phi_k\rangle = d_k`$ and 

```math
\langle \phi_k - d_k U|0\rangle, \phi_l - d_l U|0\rangle\rangle = \frac12 ((M M^T)_{kl} + i\Omega_{kl}).
```

So twice the real part of the left side, the symmetrized covariance $`\langle\{\hat R_k - d_k, \hat R_l - d_l\}\rangle`$, is $`\gamma_{kl}`$ with $`\gamma = M M^T`$, and the $`\Gamma`$ of Tjoa and Cirac is $`\gamma/2`$.  
<sub>`Sealed.gaussianUnitary_vacuum`</sub>

**100.** The two definitions of pure Gaussian states agree: $`\psi = U|0\rangle`$ for a Gaussian unitary $`U`$ if and only if $`\psi`$ has the Gaussian characteristic function with some $`(d, \gamma)`$. If $`\psi`$ has it with $`(d, \gamma)`$ and $`M`$ is symplectic with $`\gamma = M M^T`$, then $`\psi = U|0\rangle`$ for a Gaussian unitary $`U`$ with data $`(M, d)`$.  
<sub>`Sealed.isPureGaussian_iff`</sub>

**101.** The vacuum component: every pure Gaussian state $`\psi = U|0\rangle`$ has a nonzero coefficient $`\psi(0)`$ at the vacuum configuration, its component along $`|0\rangle`$. Hence a nonzero $`\Phi`$ with $`\Phi(0) = 0`$, for example a number state $`|m\rangle`$ with $`m \ne 0`$, is not a multiple $`c\psi`$ of a pure Gaussian state $`\psi`$.  
<sub>`Sealed.pureGaussian_vacuum_ne_zero`</sub>

## Further examples: Fock space and pure Gaussian states

These examples show that the hypotheses of entries 70 and 71, and the hypothesis of a Gaussian characteristic function in entries 97 to 101, can be met; Gaussian unitaries exist by entry 93.

**102.** The ladder operators are coefficient-finite, so that entries 70 and 71 apply to $`a_j`$ and $`a_j^\dagger`$.  
<sub>`Sealed.witness_ladder_coeffFinite`</sub>

**103.** The vacuum: on $`n`$ modes the vacuum $`|0\rangle`$ has the Gaussian characteristic function with $`d = 0`$ and $`\gamma = 1`$.  
<sub>`Sealed.witness_vacuum`</sub>

**104.** A coherent state: for $`\alpha \in \mathbb C^n`$ the coherent state $`D(\alpha)|0\rangle`$ has the coefficients 

```math
(D(\alpha)|0\rangle)(m) = e^{-|\alpha|^2/2} \alpha^m/\sqrt{m!}
```

and the Gaussian characteristic function with the displacement vector 

```math
\delta(\alpha) = \sqrt2\, (\mathrm{Re}\, \alpha, \mathrm{Im}\, \alpha)
```

and the vacuum covariance $`\gamma = 1`$.  
<sub>`Sealed.witness_coherent_state`</sub>

**105.** A squeezed vacuum: on one mode, for real $`r`$, the squeezed vacuum $`\mathsf S(r)|0\rangle`$ has the Gaussian characteristic function with $`d = 0`$ and the covariance matrix $`\gamma = \mathrm{diag}(e^{-2r}, e^{2r})`$. For $`r > 0`$ the position quadrature is squeezed, $`\gamma_{qq} = e^{-2r} < 1`$; $`r`$ may have either sign.  
<sub>`Sealed.witness_squeezed_vacuum`</sub>

## Existence of pure Gaussian states

The notation is that of the section on pure Gaussian states.

**106.** Every admissible symplectic covariance matrix occurs: let $`\gamma`$ be admissible and symplectic, $`\gamma \Omega \gamma^T = \Omega`$, and let $`d \in \mathbb R^{2n}`$. There is a Gaussian unitary $`U`$, with data $`(M, d)`$ for some symplectic $`M`$, such that $`U|0\rangle`$ has the Gaussian characteristic function with displacement vector $`d`$ and covariance matrix $`\gamma`$. Hence a vector with the Gaussian characteristic function with $`(d, \gamma)`$ exists if and only if $`\gamma`$ is admissible and symplectic.  
<sub>`Sealed.exists_hasGaussianCharFun_iff`</sub>

## Quadratic Hamiltonians

Here $`E`$ is a complex Hilbert space, with the inner product linear in the second argument. An operator $`A`$ on $`E`$ is a linear map defined on a subspace $`\mathrm{dom}\, A`$ of $`E`$; $`A^*`$ is its adjoint, $`\overline A`$ its closure, the operator whose graph is the closure of the graph of $`A`$, and $`A \restriction E_0`$ its restriction to a subspace $`E_0`$. An operator $`A`$ is self-adjoint when $`A^* = A`$, domains included. A one-parameter group generated by $`A`$ carries the physicist's sign, $`U_t = e^{-itA}`$. On Fock space there are $`n`$ modes, $`\hat R = (\hat q, \hat p)`$ are the quadratures of entry 95, normalized so that $`[\hat R_k, \hat R_l] = i\Omega_{kl}`$, and $`\bar T`$ is the maximal realization of a linear map $`T`$ of the formal Fock space (entry 70). For a configuration $`m`$, $`|m| = \sum_j m_j`$ is its number of particles.

**107.** One-parameter unitary groups and their generators (definitions): a map $`t \mapsto U_t`$ from $`\mathbb R`$ to the unitary operators of $`E`$ is a strongly continuous one-parameter unitary group when $`U_0 = 1`$, $`U_{s+t} = U_s U_t`$ for all real $`s`$, $`t`$, and $`t \mapsto U_t\psi`$ is continuous for every $`\psi`$. An operator $`A`$ generates $`U`$, written $`U_t = e^{-itA}`$, when $`U`$ is such a group, $`\mathrm{dom}\, A`$ is the set of the $`\psi`$ at which $`t \mapsto U_t\psi`$ is differentiable at $`t = 0`$, and 

```math
\frac{d}{dt} U_t\psi\big|_{t=0} = -iA\psi
```

for these $`\psi`$.  
<sub>`Sealed.isGenerator_iff`</sub>

**108.** Generators, first properties: let $`A`$ generate $`U`$. For $`\psi \in \mathrm{dom}\, A`$ and every real $`t`$, $`U_t\psi \in \mathrm{dom}\, A`$ with $`AU_t\psi = U_tA\psi`$, and 

```math
\frac{d}{dt} U_t\psi = -iU_tA\psi.
```

The domain of $`A`$ is dense, and $`A`$ is self-adjoint. If $`A`$ also generates $`V`$, then $`U = V`$.  
<sub>`Sealed.isGenerator_props`</sub>

**109.** Generators from a core, conjugates, shifts and bounded generators. Let $`B`$ be self-adjoint and $`E_0 \subseteq \mathrm{dom}\, B`$ a subspace with $`\overline{B \restriction E_0} = B`$ (a core for $`B`$). If $`V`$ is a strongly continuous one-parameter unitary group with 

```math
\frac{d}{dt} V_t\psi\big|_{t=0} = -iB\psi
```

for every $`\psi \in E_0`$, then $`B`$ generates $`V`$. Let $`A`$ generate $`U`$. For a unitary $`Z`$, the operator $`Z^*AZ`$ with domain $`\{\psi : Z\psi \in \mathrm{dom}\, A\}`$ generates $`t \mapsto Z^*U_tZ`$; for real $`c`$, the operator $`A + c`$ with domain $`\mathrm{dom}\, A`$ generates $`t \mapsto e^{-itc}U_t`$. A bounded self-adjoint operator $`T`$ generates 

```math
t \mapsto e^{-itT} = \sum_{k \ge 0} (-itT)^k/k!.
```  
<sub>`Sealed.isGenerator_of_core`</sub>

**110.** Analytic vectors with a common radius: let $`E_0 \subseteq E`$ be a dense subspace, $`A : E_0 \to E_0`$ linear and symmetric, $`\langle Ax, y\rangle = \langle x, Ay\rangle`$ for $`x, y \in E_0`$, and $`\rho > 0`$ with 

```math
\sum_n \rho^n \|A^n x\|/n! < \infty
```

for every $`x \in E_0`$. Regard $`A`$ as an operator on $`E`$ with domain $`E_0`$. Then its closure $`\overline A`$ is self-adjoint, $`\overline A`$ generates exactly one strongly continuous one-parameter unitary group $`U`$, and 

```math
U_t x = \sum_n (-it)^n A^n x/n!
```

for $`|t| < \rho`$ and $`x \in E_0`$.  
<sub>`Sealed.analytic_vectors`</sub>

**111.** The quadratic Hamiltonian (definitions) and its first properties: $`\mathcal D`$ is the subspace of the finitely supported vectors of $`\Gamma_s(n)`$, the $`\psi`$ with $`\psi(m) \ne 0`$ for only finitely many configurations $`m`$. For a real $`2n \times 2n`$ matrix $`K`$ and $`f \in \mathbb R^{2n}`$, the quadratic Hamiltonian is the linear map 

```math
H = \sum_{k,l} \frac12 K_{kl} \hat R_k \hat R_l + \sum_k f_k \hat R_k
```

of the formal Fock space. Let 

```math
C_H = \sum_{k,l} |K_{kl}| + \sqrt2 \sum_k |f_k|.
```

If $`\psi \in \Gamma_s(n)`$ vanishes above $`\nu`$ particles, $`\psi(m) = 0`$ whenever $`|m| > \nu`$, then $`H\jmath\psi = \jmath\varphi`$ for a $`\varphi \in \Gamma_s(n)`$ that vanishes above $`\nu + 2`$ particles, with $`\|\varphi\| \le C_H(\nu + 2)\|\psi\|`$. For $`\psi \in \mathcal D`$ and $`\rho \ge 0`$ with $`2C_H\rho < 1`$ there are $`\psi_r \in \Gamma_s(n)`$, $`r \in \mathbb N`$, with $`\jmath\psi_r = H^r\jmath\psi`$ and 

```math
\sum_r \rho^r \|\psi_r\|/r! < \infty.
```

If $`K`$ is symmetric, $`H`$ is symmetric on $`\mathcal D`$: for $`\psi, \varphi \in \mathcal D`$, $`\langle H\psi, \varphi\rangle = \langle \psi, H\varphi\rangle`$, where $`H\psi`$ is the vector $`\psi'`$ with $`\jmath\psi' = H\jmath\psi`$.  
<sub>`Sealed.quadraticHamiltonian_eq`</sub>

**112.** Commutators: on the formal Fock space $`[\hat R_k, \hat R_l] = i\Omega_{kl}`$. Let $`K`$ be symmetric. Then 

```math
[\hat R_k, H] = i\big(\sum_m (\Omega K)_{km} \hat R_m + (\Omega f)_k\big),
```

and for $`v \in \mathbb R^{2n}`$ the field 

```math
\Phi_v = \sigma(v, \hat R) = \sum_i (\Omega^T v)_i \hat R_i
```

satisfies 

```math
[\Phi_v, H] = -i(\Phi_{\Omega K v} + f^T v).
```  
<sub>`Sealed.quadraticHamiltonian_commutators`</sub>

**113.** Essential self-adjointness and the unitary group: let $`K`$ be symmetric, let $`\bar H`$ be the maximal realization of $`H`$, and $`\bar H \restriction \mathcal D`$ its restriction to the finitely supported vectors. Then $`\bar H`$ is self-adjoint and is the closure of $`\bar H \restriction \mathcal D`$, and $`(\bar H \restriction \mathcal D)^* = \bar H`$. The operator $`\bar H`$ generates exactly one strongly continuous one-parameter unitary group, $`t \mapsto e^{-it\bar H}`$. For $`\psi \in \mathcal D`$ and $`2C_H|t| < 1`$, 

```math
e^{-it\bar H}\psi = \sum_r (-it)^r \psi_r/r!,
```

with $`C_H`$ and the vectors $`\psi_r`$, $`\jmath\psi_r = H^r\jmath\psi`$, of entry 111.  
<sub>`Sealed.quadraticHamiltonian_isSelfAdjoint`</sub>

**114.** Quadratic Hamiltonians generate Gaussian unitaries: let $`K`$ be symmetric and $`U_t = e^{-it\bar H}`$ the group generated by $`\bar H`$ (entry 113). Let $`M(t) = e^{t\Omega K}`$ and 

```math
d(t) = \int_0^t M(s)\Omega f\, ds;
```

these give the flow $`x(t) = M(t)x(0) + d(t)`$ of the classical equations of motion $`\dot x = \Omega K x + \Omega f`$ of the Hamilton function $`\frac12 x^T K x + f^T x`$ (a remark that is not part of the statement). For every real $`t`$, $`U_t`$ is a Gaussian unitary with data $`(M(t), d(t))`$: 

```math
e^{it\bar H} W(u) e^{-it\bar H} = e^{-i\sigma(u, d(t))} W(M(t)^{-1}u)
```

for every $`u \in \mathbb R^{2n}`$. In particular $`e^{-i\bar H}`$ has data $`(e^{\Omega K}, d(1))`$, and by entry 95 

```math
e^{i\bar H} \hat R e^{-i\bar H} = e^{\Omega K} \hat R + d(1)
```

on the vectors in the domain of every $`\bar a_j`$, Eq. (3) of Tjoa and Cirac.  
<sub>`Sealed.quadraticHamiltonian_isGaussianUnitary`</sub>

**115.** Eqs. (1) and (5) of Tjoa and Cirac. (Definitions) For complex $`n \times n`$ matrices $`h`$, $`\Delta`$ and $`\eta \in \mathbb C^n`$, the Hamiltonian of Eq. (1) is the linear map 

```math
H_G = \sum_{i,j} h_{ij} a_i^\dagger a_j + \frac12 \sum_{i,j} (\Delta_{ij} a_i^\dagger a_j^\dagger + \bar\Delta_{ij} a_i a_j) + \sum_j (\eta_j a_j^\dagger + \bar\eta_j a_j)
```

of the formal Fock space, and its matrix is 

```math
K = \begin{pmatrix} \mathrm{Re}\, h + \mathrm{Re}\, \Delta & \mathrm{Im}\, \Delta - \mathrm{Im}\, h \\ \mathrm{Im}\, \Delta + \mathrm{Im}\, h & \mathrm{Re}\, h - \mathrm{Re}\, \Delta \end{pmatrix}.
```

Let $`h`$ be Hermitian and $`\Delta`$ symmetric, and let $`H`$ be the quadratic Hamiltonian of $`K`$ and $`f = \delta(\eta)`$, with 

```math
\delta(\eta) = \sqrt2\, (\mathrm{Re}\, \eta, \mathrm{Im}\, \eta)
```

as in entry 93. Then $`K`$ is symmetric and 

```math
H_G = H - \frac12 \mathrm{tr}\, h.
```

The maximal realization $`\bar H_G`$ is self-adjoint and generates exactly one strongly continuous one-parameter unitary group, and for every real $`\theta`$ the operator $`e^{i\theta} e^{-i\bar H_G}`$ is a Gaussian unitary with data $`(e^{\Omega K}, d(1))`$, where 

```math
d(1) = \int_0^1 e^{s\Omega K}\Omega f\, ds.
```

For $`\alpha, \zeta \in \mathbb C^n`$, the maximal realizations $`A_\alpha`$ of $`i \sum_j (\alpha_j a_j^\dagger - \bar\alpha_j a_j)`$ and $`B_\zeta`$ of $`\frac i2 \sum_j (\bar\zeta_j a_j^2 - \zeta_j a_j^{\dagger 2})`$ generate $`s \mapsto D(s\alpha)`$ and $`s \mapsto \mathsf S(s\zeta)`$: $`D(\alpha) = e^{-iA_\alpha}`$ and $`\mathsf S(\zeta) = e^{-iB_\zeta}`$, which Eq. (5) writes as $`e^{\alpha \cdot a^\dagger - \bar\alpha \cdot a}`$ and $`e^{\frac12 \sum_j (\bar\zeta_j a_j^2 - \zeta_j a_j^{\dagger 2})}`$.  
<sub>`Sealed.ladderHamiltonian_isGaussianUnitary`</sub>

---

SHA-256 of `verify/Challenge.lean` (LF line endings): `e81d0bd0259599b101767bd97ec62bbc9e381a736a7257a7eac257b55d926586`
