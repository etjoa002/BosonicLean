# The sealed statements

Generated from `verify/Challenge.lean` by `verify/make_core_page.py`: the 67 statements that `lake comparator` checks (see the section "Verification" of the front page). Each entry gives the statement in words and the name of its formal version in `Challenge.lean`.

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

**8.** Let $`s > 0`$, $`\hbar > 0`$ and $`\psi(x) = (\sqrt{\pi}\, s)^{-1/2} e^{-x^2/(2s^2)}`$ on $`\mathbb R`$. Then $`\int |\psi|^2\, dx = 1`$. Let $`A_q \psi = x\psi`$ and $`A_p \psi = -i\hbar\psi'`$ be the position and momentum applied to $`\psi`$, $`m_j = \mathrm{Re} \int \bar\psi\, A_j\psi\, dx`$ their means, and $`\gamma_{jk} = 2\, \mathrm{Re} \int \overline{(A_j\psi - m_j\psi)}\, (A_k\psi - m_k\psi)\, dx`$ for $`j, k \in \{q, p\}`$. Then $`\gamma = \mathrm{diag}(s^2, \hbar^2/s^2)`$.  
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

$`V`$ is a real vector space and $`\sigma`$ a real bilinear form on $`V`$. The form $`\sigma`$ is alternating when $`\sigma(u, u) = 0`$ for every $`u`$. It is nondegenerate when $`\sigma(u, \cdot) = 0`$ only for $`u = 0`$ and $`\sigma(\cdot, w) = 0`$ only for $`w = 0`$; for alternating $`\sigma`$ the two conditions coincide. The Hilbert space $`\ell^2(V)`$ consists of the functions $`f : V \to \mathbb C`$ with $`\sum_{v \in V} |f(v)|^2 < \infty`$, that is, $`\ell^2`$ of $`V`$ with the discrete topology; bounded operators carry the operator norm and the adjoint as star. The matrix $`\Omega`$ of the covariance sections is the matrix of $`\sigma`$ in the coordinates $`(q, p)`$ of $`V = \mathbb R^{2n}`$, $`\sigma(u, w) = u^T \Omega w`$ with $`\Omega`$ as in entry 1; on one mode this is the form $`\sigma(u, w) = u_1 w_2 - u_2 w_1`$ of entry 32.

**14.** The Weyl operators and the CCR algebra: let $`\sigma`$ be any real bilinear form on $`V`$. For $`u \in V`$ the Weyl operator $`W(u)`$ is the bounded operator on $`\ell^2(V)`$ with $`(W(u) f)(v) = e^{i\sigma(u, v)/2} f(v + u)`$, and the CCR algebra $`\mathrm{CCR}(V, \sigma)`$ is the norm closure of the star subalgebra generated by the Weyl operators.  
<sub>`Sealed.weyl_apply_and_CCR_eq`</sub>

**15.** For alternating $`\sigma`$, every Weyl operator is unitary, $`W(u)^* = W(-u)`$, and the Weyl relation $`W(u) W(w) = e^{-i\sigma(u, w)/2} W(u + w)`$ holds.  
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

**20.** A necessary condition for Gaussian states: let $`\sigma`$ be alternating and $`\omega`$ a state on $`\mathrm{CCR}(V, \sigma)`$ that is Gaussian with symmetric covariance form $`\gamma`$ and linear displacement $`d`$, that is $`\omega(W(u)) = \exp(i d(u) - \gamma(u, u)/4)`$ for every $`u`$. Then the data $`(d, \gamma)`$ satisfy all three of the following: (i) $`\gamma + i\sigma \ge 0`$, that is, for every finite family $`u_1, \dots, u_m`$ of vectors the complex matrix $`(\gamma(u_j, u_k) + i \sigma(u_j, u_k))_{jk}`$ is positive semidefinite; (ii) $`\gamma(u, u) \ge 0`$ for every $`u`$; (iii) $`\sigma(u, w)^2 \le \gamma(u, u) \gamma(w, w)`$ for all $`u, w`$. Conditions (ii) and (iii) follow from (i) with $`m = 1`$ and $`m = 2`$. The condition is necessary: every Gaussian state has data satisfying it. The existence of a Gaussian state for data satisfying the condition is a candidate for a later theorem.  
<sub>`Sealed.gaussian_state_condition`</sub>

## Gaussian channels

A Gaussian channel on $`\mathrm{CCR}(V, \sigma)`$ has data $`(L, \nu, \mu)`$: a linear map $`L : V \to V`$, a symmetric bilinear form $`\nu`$ and a linear form $`\mu`$, satisfying the channel condition $`\nu + i\sigma - i\sigma(L\cdot, L\cdot) \ge 0`$ (every finite Gram matrix positive semidefinite), together with a completely positive map $`f`$ of the CCR algebra with $`f(W(u)) = \exp(i\mu(u) - \nu(u, u)/4)\, W(Lu)`$. A complex-linear map $`f`$ of the CCR algebra is completely positive when every matrix amplification $`(a_{jk}) \mapsto (f(a_{jk}))`$ on $`k \times k`$ matrices with entries in the CCR algebra is positive. The order on the CCR algebra is that of the bounded operators. Complete positivity of the maps is a hypothesis.

**21.** Composition: let $`\sigma`$ be any real bilinear form on $`V`$, and let $`(L_1, \nu_1, \mu_1, f_1)`$ and $`(L_2, \nu_2, \mu_2, f_2)`$ be Gaussian channels. Then $`a \mapsto f_2(f_1(a))`$ is completely positive and is the Gaussian channel with data $`L = L_2 L_1`$, $`\nu = \nu_1 + \nu_2(L_1\cdot, L_1\cdot)`$ and $`\mu = \mu_1 + \mu_2 \circ L_1`$: $`\nu`$ is symmetric, the data satisfy the channel condition, and $`f_2(f_1(W(u))) = \exp(i\mu(u) - \nu(u, u)/4)\, W(Lu)`$.  
<sub>`Sealed.gaussianChannel_comp`</sub>

**22.** Channel matrices: for $`n`$ modes, let $`X`$ and $`Y`$ be real $`2n \times 2n`$ matrices with $`Y`$ symmetric and $`Y - i\Omega + iX\Omega X^T \ge 0`$. Then $`X \gamma X^T + Y`$ is admissible for every admissible $`\gamma`$.  
<sub>`Sealed.isAdmissible_channel`</sub>

## The formal Fock space

The modes form a type $`\iota`$, an occupation-number configuration is a finitely supported $`n : \iota \to \mathbb N`$ (finitely supported), with $`|n| = \sum_i n_i`$ and $`n! = \prod_i n_i!`$, and $`e_i`$ is the configuration with one particle in mode $`i`$. The coefficients lie in a complex vector space $`R`$, which for the Bargmann map and in entry 34 is a ring and a complex algebra. A raising operator is a complex-linear map $`T`$ of the formal Fock space that raises the degree of vanishing: if $`\psi(n) = 0`$ for all $`|n| < k`$, then $`(T\psi)(n) = 0`$ for all $`|n| < k + 1`$. Entry 25 characterizes these maps and defines their exponential.

**23.** The formal Fock space is the space of all coefficient families: $`\psi \mapsto (\psi(n))_n`$ is a complex-linear bijection from the formal Fock space onto all functions from occupation numbers to $`R`$, with no summability condition. The creation operator is $`(a_i^\dagger \psi)(n) = \sqrt{n_i}\, \psi(n - e_i)`$ if $`n_i > 0`$ and $`0`$ otherwise, and the annihilation operator is $`(a_i \psi)(n) = \sqrt{n_i + 1}\, \psi(n + e_i)`$.  
<sub>`Sealed.formalFock_and_ladder`</sub>

**24.** The canonical commutation relations on the whole formal Fock space: $`[a_i, a_j^\dagger] = \delta_{ij}`$, $`[a_i, a_j] = 0`$ and $`[a_i^\dagger, a_j^\dagger] = 0`$.  
<sub>`Sealed.ccr_ladder`</sub>

**25.** Raising operators and their exponential: a linear map $`T`$ of the formal Fock space is a raising operator if and only if, whenever $`\psi(n) = 0`$ for all $`|n| < k`$, also $`(T\psi)(n) = 0`$ for all $`|n| < k + 1`$. For a raising operator $`T`$ the exponential is $`(e^T \psi)(n) = \sum_{k=0}^{|n|} (T^k \psi)(n) / k!`$, a finite sum.  
<sub>`Sealed.raisingOp_and_raisingExp`</sub>

**26.** The exponential law: for raising operators $`S`$ and $`T`$ whose underlying maps commute, the raising operator $`S + T`$ has as underlying map the sum of theirs, and $`e^{S+T} = e^S e^T`$.  
<sub>`Sealed.raisingExp_add`</sub>

**27.** The Bargmann map $`\mathfrak B`$ sends $`\psi`$ to the formal power series $`\sum_n \psi(n)\, z^n / \sqrt{n!}`$; it is, by its type, a complex-linear bijection onto all formal power series in variables $`z_i`$ ($`i \in \iota`$) with coefficients in $`R`$.  
<sub>`Sealed.coeff_toBargmann`</sub>

**28.** The Bargmann map turns $`a_j^\dagger`$ into multiplication by $`z_j`$ and $`a_j`$ into the partial derivative $`\partial_j = \partial / \partial z_j`$ defined on coefficients by $`(\partial_j f)_n = (n_j + 1)\, f_{n + e_j}`$.  
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

**34.** The creation operator $`a_j^\dagger`$ is a raising operator.  
<sub>`Sealed.witness_create_raising`</sub>

**35.** The identity channel: let $`\sigma`$ be any real bilinear form on $`V`$. The data $`L = \mathrm{id}`$, $`\nu = 0`$, $`\mu = 0`$ satisfy the hypotheses that entry 21 places on each channel: $`\nu`$ is symmetric, the channel condition holds (every Gram matrix is $`0`$), and the identity map $`f(a) = a`$ of $`\mathrm{CCR}(V, \sigma)`$ is completely positive with $`f(W(u)) = \exp(i\mu(u) - \nu(u, u)/4)\, W(Lu) = W(u)`$.  
<sub>`Sealed.witness_identity_channel`</sub>

**36.** The identity automorphism: let $`\sigma`$ be any real bilinear form on $`V`$. The identity $`\mathbb C`$-linear star automorphism $`T`$ of $`\mathrm{CCR}(V, \sigma)`$, with $`\Gamma = \mathrm{id}`$ and $`c = 1`$, satisfies $`T(W(u)) = c(u)\, W(\Gamma u)`$ for every $`u`$. Together with entry 32 it gives an instance of the hypotheses of entry 18.  
<sub>`Sealed.witness_identity_automorphism`</sub>

## The Gaussian wave function: Schwartz domain, moments and units

A Schwartz function is a smooth function $`\mathbb R \to \mathbb C`$ whose derivatives of every order decay faster than every power of $`|x|`$; it is square integrable, and its class in $`L^2(\mathbb R)`$ carries the $`L^2`$ norm. The Schwartz functions form a common domain for the position $`x\psi`$ and the momentum $`-i\hbar\psi'`$. Throughout this section $`\psi(x) = (\sqrt{\pi}\, s)^{-1/2} e^{-x^2/(2s^2)}`$ is the Gaussian of entry 8, of width $`s > 0`$.

**37.** Let $`s > 0`$ and $`\psi(x) = (\sqrt{\pi}\, s)^{-1/2} e^{-x^2/(2s^2)}`$. Then $`\psi`$ is a Schwartz function (exactly one Schwartz function equals $`\psi`$ at every point), and its class in $`L^2(\mathbb R)`$ has norm $`1`$.  
<sub>`Sealed.gaussian_schwartz_unique`</sub>

**38.** Moments: let $`s > 0`$, $`\hbar > 0`$ and $`\psi(x) = (\sqrt{\pi}\, s)^{-1/2} e^{-x^2/(2s^2)}`$. Then $`x\psi`$ and $`-i\hbar\psi'`$ are Schwartz functions, and $`-i\hbar\psi'(x) = (i\hbar/s^2)\, x\psi(x)`$ for every $`x`$. The first moments vanish, $`\int \bar\psi\, x\psi\, dx = 0`$ and $`\int \bar\psi\, (-i\hbar\psi')\, dx = 0`$, and the second moments are $`\int |x\psi|^2\, dx = s^2/2`$, $`\int |{-i\hbar\psi'}|^2\, dx = \hbar^2/(2s^2)`$ and $`\int \overline{x\psi}\, (-i\hbar\psi')\, dx = i\hbar/2`$.  
<sub>`Sealed.gaussian_moments`</sub>

**39.** Dimensionless units: for $`s > 0`$ and $`\hbar > 0`$ let $`D = \mathrm{diag}(1/s, s/\hbar)`$, the rescaling $`q \mapsto q/s`$, $`p \mapsto sp/\hbar`$ of position and momentum. Then $`D\, \mathrm{diag}(s^2, \hbar^2/s^2)\, D^T = 1`$: in these units the covariance of entry 8 is the vacuum covariance $`1`$.  
<sub>`Sealed.gaussian_dimensionless`</sub>

**40.** The width $`s^2 = \hbar/(m\omega)`$: let $`m > 0`$, $`\omega > 0`$, $`\hbar > 0`$ and $`s = \sqrt{\hbar/(m\omega)}`$. Let $`\psi`$, $`A_q\psi = x\psi`$, $`A_p\psi = -i\hbar\psi'`$ and the matrix $`\gamma`$ be as in entry 8 for this $`s`$. Then $`\gamma = \mathrm{diag}(\hbar/(m\omega), \hbar m\omega)`$.  
<sub>`Sealed.gaussian_oscillator`</sub>

## Fourier analysis, product covariances and Gaussian kernels

A periodic chain is homogeneous when every site carries the same local matrix $`\Gamma`$; its contracted covariance $`\gamma`$ is that of entries 9 and 13 with input matrix of entry 11. The sites are $`x, y \in \{0, \dots, N - 1\}`$, and $`a_x`$ for $`a \in \{q, p\}`$ denotes the position or momentum coordinate of the physical mode of site $`x`$. For $`k \in \{0, \dots, N - 1\}`$ the character of $`\mathbb Z/N`$ is $`\chi_k(x) = e^{-2\pi i k x/N}`$. A complex matrix $`E`$ is positive definite when it is Hermitian with $`\bar z^T E z > 0`$ for every nonzero complex vector $`z`$, and $`H^*`$ is the conjugate transpose of $`H`$.

**41.** The symbols of a homogeneous chain: let $`\Gamma`$ be a real $`2(2M+1) \times 2(2M+1)`$ matrix, regarded as complex, and $`\Gamma_{VV}`$, $`\Gamma_{VC}`$, $`\Gamma_{CC}`$ its blocks on the coordinates of the virtual modes and of the physical mode: the virtual coordinates are listed as the positions and then the momenta of the modes $`A_a`$ (local mode $`a < M`$), followed by the positions and then the momenta of the modes $`B_a`$ (local mode $`M + a`$); the physical coordinates are those of local mode $`2M`$. For $`k`$ let $`\tau`$ be the diagonal $`2M \times 2M`$ matrix with entries $`1`$ on positions and $`-1`$ on momenta, and $`S_k = (1 \mid e^{-2\pi i k/N}\tau)`$ the $`2M \times 4M`$ matrix whose first $`2M`$ columns, those of the coordinates of the modes $`A_a`$, form the identity matrix and whose last $`2M`$ columns, those of the coordinates of the modes $`B_a`$, form $`e^{-2\pi i k/N}\tau`$. The eliminated symbol is $`E_k = S_k \Gamma_{VV} S_k^*`$, and the covariance symbol is the $`2 \times 2`$ complex matrix $`\Sigma_k = \Gamma_{CC} - (S_k\Gamma_{VC})^* E_k^{-1} (S_k\Gamma_{VC})`$, where $`E_k^{-1}`$ is the matrix inverse.  
<sub>`Sealed.covarianceSymbol_eq`</sub>

**42.** Fourier block diagonalization: let $`N \ge 3`$, $`M \ge 1`$, $`\Gamma`$ admissible on $`2M + 1`$ modes, and $`\gamma`$ the contracted covariance of the homogeneous periodic chain with local matrix $`\Gamma`$ at every site. Then $`\gamma`$ is invariant under the rotation $`x \mapsto x + 1 \bmod N`$ of the sites, $`\gamma(a_{x+1}, b_{y+1}) = \gamma(a_x, b_y)`$ for $`a, b \in \{q, p\}`$; every eliminated symbol $`E_k`$ is positive definite; and the Fourier transform of $`\gamma`$ is block diagonal with the covariance symbols as blocks: $`\frac1N \sum_{x, y} \chi_k(x)\, \gamma(a_x, b_y)\, \overline{\chi_l(y)} = \delta_{kl}\, \Sigma_k(a, b)`$ for all $`k, l`$ and $`a, b \in \{q, p\}`$.  
<sub>`Sealed.fourier_block_diagonal`</sub>

**43.** Fourier reconstruction: under the hypotheses of entry 42, $`\gamma(a_x, b_y) = \frac1N \sum_k \overline{\chi_k(x)}\, \Sigma_k(a, b)\, \chi_k(y)`$ for all sites $`x, y`$ and $`a, b \in \{q, p\}`$; every covariance symbol satisfies $`\Sigma_k - i\Omega \ge 0`$, with $`\Omega`$ the symplectic matrix of one mode; and $`\Sigma_l`$ is the entrywise complex conjugate of $`\Sigma_k`$ whenever $`k + l \equiv 0 \pmod N`$.  
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

Let $`\mathcal A`$ be a unital C*-algebra. A Weyl system for $`(V, \sigma)`$ in $`\mathcal A`$ is a map $`W : V \to \mathcal A`$ such that every $`W(u)`$ is unitary, the Weyl relation $`W(u) W(w) = e^{-i\sigma(u, w)/2} W(u + w)`$ holds, and the $`W(u)`$ generate $`\mathcal A`$: the norm closure of the star subalgebra generated by them is $`\mathcal A`$. A representation of a C*-algebra $`\mathcal A`$ on a complex Hilbert space $`H`$ is a $`\mathbb C`$-linear unital star homomorphism $`\pi`$ from $`\mathcal A`$ to the bounded operators on $`H`$.

**50.** Let $`\sigma`$ be alternating and $`W`$ a Weyl system for $`(V, \sigma)`$ in a unital C*-algebra $`\mathcal A`$. Then $`W(0) = 1`$, $`W(u)^* = W(-u)`$, $`W(u) W(w) = e^{-i\sigma(u, w)} W(w) W(u)`$ for all $`u, w`$, and $`W(u)`$ and $`W(w)`$ commute whenever $`\sigma(u, w) = 0`$.  
<sub>`Sealed.weylSystem_relations`</sub>

**51.** The CCR algebra is a Weyl system: for alternating $`\sigma`$ the Weyl operators $`W(u)`$, as elements of $`\mathrm{CCR}(V, \sigma)`$, form a Weyl system for $`(V, \sigma)`$ in $`\mathrm{CCR}(V, \sigma)`$.  
<sub>`Sealed.weylSystem_CCR`</sub>

**52.** Pullback of a Weyl system: let $`\sigma`$ and $`\sigma_0`$ be real bilinear forms on $`V`$ and $`V_0`$, $`W`$ a Weyl system for $`(V_0, \sigma_0)`$ in a unital C*-algebra $`\mathcal A`$, and $`T : V \to V_0`$ a linear map with $`\sigma_0(Tu, Tw) = \sigma(u, w)`$. Then every $`W(Tu)`$ is unitary and $`u \mapsto W(Tu)`$ satisfies the Weyl relation of $`\sigma`$; if $`T`$ is surjective, the $`W(Tu)`$ generate $`\mathcal A`$, so that $`u \mapsto W(Tu)`$ is a Weyl system for $`(V, \sigma)`$.  
<sub>`Sealed.weylSystem_pullback`</sub>

**53.** The relabelling maps: let $`\sigma`$ and $`\sigma'`$ be real bilinear forms on $`V`$ and $`V'`$, and $`T : V \to V'`$ a linear bijection with $`\sigma'(Tu, Tv) = \sigma(u, v)`$. The relabelling unitary $`U_T`$, a linear isometric bijection $`\ell^2(V) \to \ell^2(V')`$, is $`(U_T f)(v') = f(T^{-1}v')`$, and the relabelling $`\alpha_T`$, a $`\mathbb C`$-linear star isomorphism $`\mathrm{CCR}(V, \sigma) \to \mathrm{CCR}(V', \sigma')`$, is $`\alpha_T(a) = U_T\, a\, U_T^{-1}`$.  
<sub>`Sealed.relabel_eq`</sub>

**54.** Relabelling is functorial: let $`\sigma`$, $`\sigma'`$, $`\sigma''`$ be real bilinear forms on $`V`$, $`V'`$, $`V''`$, and $`T_1 : V \to V'`$, $`T_2 : V' \to V''`$ linear bijections with $`\sigma'(T_1u, T_1v) = \sigma(u, v)`$ and $`\sigma''(T_2u', T_2v') = \sigma'(u', v')`$. Then $`\alpha_{T_1}(W(u)) = W'(T_1u)`$ for every $`u \in V`$, the relabelling by the identity of $`V`$ is the identity of $`\mathrm{CCR}(V, \sigma)`$, and $`\alpha_{T_2 T_1} = \alpha_{T_2} \circ \alpha_{T_1}`$.  
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

Gaussian channels $`(L, \nu, \mu, f)`$ are as in the section on Gaussian channels; their dissipation form is $`C(u, w) = \nu(u, w) + i\sigma(u, w) - i\sigma(Lu, Lw)`$. A C*-algebra with a partial order is star-ordered when $`a \le b`$ holds exactly if $`b = a + p`$ for a finite sum $`p`$ of elements of the form $`s^* s`$.

**59.** The product formula: let $`\sigma`$ be alternating and $`(L, \nu, \mu, f)`$ a Gaussian channel on $`\mathrm{CCR}(V, \sigma)`$. Then $`f(W(u) W(w)) = e^{-C(u, w)/2}\, f(W(u))\, f(W(w))`$ for all $`u, w \in V`$.  
<sub>`Sealed.gaussianChannel_product`</sub>

**60.** Channels and Gaussian states: let $`\sigma`$ be any real bilinear form on $`V`$, $`(L, \nu, \mu, f)`$ a Gaussian channel on $`\mathrm{CCR}(V, \sigma)`$, and $`\omega`$ a given state that is Gaussian with symmetric covariance form $`\gamma`$ and linear displacement $`d`$, that is $`\omega(W(u)) = \exp(i d(u) - \gamma(u, u)/4)`$. Then $`\omega'(a) = \omega(f(a))`$ defines a state $`\omega'`$, and $`\omega'`$ is Gaussian with the symmetric covariance form $`\gamma(L\cdot, L\cdot) + \nu`$ and the displacement $`d \circ L + \mu`$: $`\omega'(W(u)) = \exp(i (d(Lu) + \mu(u)) - (\gamma(Lu, Lu) + \nu(u, u))/4)`$. The statement assumes the Gaussian state $`\omega`$; the library constructs no Gaussian state, and the existence of Gaussian states is a candidate for a later theorem, as in entry 20. Apart from states obtained from given ones, as here, the only state constructed is the vector state of entry 67, which is not Gaussian for $`V \ne 0`$, since its characteristic function vanishes away from $`0`$.  
<sub>`Sealed.gaussianChannel_state`</sub>

**61.** No noise: let $`\sigma`$ be alternating and $`L : V \to V`$ a linear map such that the data $`(L, 0)`$ satisfy the channel condition, that is, the complex matrix $`(i\sigma(u_j, u_k) - i\sigma(Lu_j, Lu_k))_{jk}`$ is positive semidefinite for every finite family $`u_1, \dots, u_m`$. Then $`L`$ preserves $`\sigma`$: $`\sigma(Lu, Lw) = \sigma(u, w)`$.  
<sub>`Sealed.noiseless_preserves`</sub>

**62.** The noiseless channel as a relabelling: let $`\sigma`$ be alternating and $`L : V \to V`$ a linear bijection with $`\sigma(Lu, Lv) = \sigma(u, v)`$. The relabelling $`\alpha_L`$ of entry 53 is completely positive, and every completely positive map $`f`$ of $`\mathrm{CCR}(V, \sigma)`$ with $`f(W(u)) = W(Lu)`$ for every $`u`$, that is, every Gaussian channel with data $`(L, 0, 0)`$, equals $`\alpha_L`$.  
<sub>`Sealed.noiseless_channel_relabel`</sub>

**63.** Dilations at the level of covariances: let $`\sigma`$ and $`\sigma'`$ be real bilinear forms on $`V`$ (the system) and $`V'`$ (the ancilla), and $`S : V \times V' \to V \times V'`$ a linear map preserving $`\sigma \oplus \sigma'`$: $`\sigma(S(x)_1, S(y)_1) + \sigma'(S(x)_2, S(y)_2) = \sigma(x_1, y_1) + \sigma'(x_2, y_2)`$. Write $`Au = S(u, 0)_1`$ and $`Cu = S(u, 0)_2`$, and let $`\gamma`$, $`\gamma'`$ be real bilinear forms on $`V`$, $`V'`$. Then (i) $`\sigma(Au, Aw) + \sigma'(Cu, Cw) = \sigma(u, w)`$; (ii) if $`\gamma' + i\sigma' \ge 0`$ on every finite family, the data $`(A, \gamma'(C\cdot, C\cdot))`$ satisfy the channel condition $`\gamma'(C\cdot, C\cdot) + i\sigma - i\sigma(A\cdot, A\cdot) \ge 0`$ on every finite family; (iii) the reduced covariance is $`(\gamma \oplus \gamma')(S(u, 0), S(w, 0)) = \gamma(Au, Aw) + \gamma'(Cu, Cw)`$, as an identity of bilinear forms.  
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

---

SHA-256 of `verify/Challenge.lean` (LF line endings): `68e93d70aa1a6ac010df82532f403d812afa7e58e7918d3328bebebcd50966c1`
