<!-- Translated from the Russian by Michal Shavit. Equation numbers follow the original. -->

*Translated from the original Russian publication [1] by Michal Shavit.*

The equations of hydrodynamics of an ideal incompressible fluid (H.I.I.F.) have the characteristic property that they are non-linear in the velocity field, and this non-linearity is of the second degree; moreover, there is a quadratic integral of motion, the energy. These equations can be written as

$$\partial_{t}\mathbf{v}=\text{rot}^{-1}\left\{ \left(\text{rot}\,\mathbf{v}\cdot\nabla\right)\mathbf{v}-\left(\mathbf{v}\cdot\nabla\right)\text{rot}\,\mathbf{v}\right\} \tag{1}$$

where the state of the system is characterized by a divergence-free velocity field $\mathbf{v}(r)$ ($\text{div}\,\mathbf{v}=0$), satisfying the boundary conditions $v_{n}=0$ on the fixed walls. The region occupied by the liquid is assumed to be finite, and the consideration is carried out in the coordinate system in which the center of gravity of the system is at rest. The symbol $\text{rot}^{-1}$ means the operator for restoring the velocity field from the vorticity field, taking into account the boundary conditions. The classical Euler equations of rigid body dynamics have the same general properties:

$$I_{1}\dot{\omega}_{1}=\left(I_{2}-I_{3}\right)\omega_{2}\omega_{3},\quad I_{2}\dot{\omega}_{2}=\left(I_{3}-I_{1}\right)\omega_{3}\omega_{1},\quad I_{3}\dot{\omega}_{3}=\left(I_{1}-I_{2}\right)\omega_{1}\omega_{2} \tag{2}$$

with the energy integral

$$2E=I_{1}\omega_{1}^{2}+I_{2}\omega_{2}^{2}+I_{3}\omega_{3}^{2}. \tag{3}$$

We use the same notation as [2]. The analogy between H.I.I.F. and rigid body dynamics (R.B.D.) has deep group-theoretical roots, as was recently demonstrated by V. I. Arnold [3]. In this paper, we define a wide class of dynamical systems, including the dynamics of a rigid body and finite-dimensional analogues of the H.I.I.F., in order to consider the problem of integral invariants, which is important for the statistical theory of turbulence.

We will call a dynamical system $S_{n}$, whose state is given by a collection of quantities $u^{1},u^{2},\dots,u^{n}$ (a vector $u^{i}$), a system of hydrodynamic type (S.H.T.) if the following three fundamental conditions are satisfied.

1. The equations of motion are quadratically non-linear and can be written with the help of a dynamical tensor of rank three,
    $$\dot{u}^{i}=\Gamma_{\lambda\mu}^{i}u^{\lambda}u^{\mu}, \tag{4}$$
    where repeated Greek indices are summed over. The dynamical tensor can always be taken symmetric with respect to its lower indices:
    $$\Gamma_{jk}^{i}=\Gamma_{kj}^{i}. \tag{5}$$

2. The volume in phase space is conserved: the flow defined by the system is incompressible,
    $$\partial\dot{u}^{\lambda}/\partial u^{\lambda}=0, \tag{6}$$
    from which follows the vanishing of the covariant vector
    $$V_{j}=\Gamma_{j\lambda}^{\lambda}=0. \tag{7}$$

3. There is (at least one) energy integral, a positive-definite quadratic form of the variables,
    $$2E=g_{\mu\nu}u^{\mu}u^{\nu}, \tag{8}$$
    with symmetric $g_{ik}$, such that
    $$dE/dt=0. \tag{9}$$
    This holds if
    $$g_{i\lambda}\Gamma_{jk}^{\lambda}+g_{j\lambda}\Gamma_{ki}^{\lambda}+g_{k\lambda}\Gamma_{ij}^{\lambda}=0; \tag{10}$$
    if we lower indices with the help of the energy tensor $g_{\mu\nu}$, this becomes
    $$\Gamma_{i,jk}+\Gamma_{j,ki}+\Gamma_{k,ij}=0, \tag{11}$$
    which is convenient to use in the "Cartesian" coordinate system, where $g_{ik}=\delta_{ik}$.

We note that the regularity condition ($V_{j}=\Gamma_{j\lambda}^{\lambda}=0$) is satisfied in the case of the infinite-dimensional dynamical system of ideal incompressible hydrodynamics, for which the phase space is a separable Hilbert space (the metric is defined by the energy integral), and the system can be approximated by an infinite sequence of dynamical systems of the type indicated above.

For hydrodynamic fields that are periodic in space, the fulfilment of condition (5) is easily proved by the fact that in the Fourier representation any term $\Gamma_{ij}^{j}$ entering the sum $\Gamma_{i\lambda}^{\lambda}$ turns out to be equal to zero. This circumstance was pointed out by Lee [4]. Note that the finite-dimensional approximations of the equations of hydrodynamics used in the numerical forecasting of meteorological fields (see, for example, [5]) also belong to the class of S.H.T. In this case the regularity condition can be easily satisfied, and in the usually employed difference schemes it holds (in the limit of an infinitely small time step).

Counting the number of conditions that the dynamical tensor $\Gamma_{jk}^{i}$ satisfies shows that the number of independent components of this tensor (for a given energy tensor) is

$$N=n\left(n+2\right)\left(n-2\right)/3, \tag{12}$$

which gives, in the simplest case of systems of hydrodynamic type with $n=3$, $N=5$.

Naturally, the question arises of the equivalence of S.H.T. and of the corresponding invariants. It can be proved that any S.H.T. with $n=3$ is equivalent to the Euler system of rigid body dynamics. By an orthogonal transformation, which leaves the energy tensor $g_{ik}=\delta_{ik}$ invariant, the dynamical tensor is reduced to the canonical form in which $\Gamma_{1,23}=p$, $\Gamma_{2,31}=q$, $\Gamma_{3,12}=r$, all other components vanish, and the quantities $p,q,r$ are related by the single relation

$$p+q+r=0. \tag{13}$$

The corresponding canonical form of the equations of motion is

$$\frac{du_{1}}{dt}=pu_{2}u_{3},\quad\frac{du_{2}}{dt}=qu_{3}u_{1},\quad\frac{du_{3}}{dt}=ru_{1}u_{2}. \tag{14}$$

Because $p+q+r=0$, besides the energy integral $2E=u_{1}^{2}+u_{2}^{2}+u_{3}^{2}$ the system has a second quadratic integral, associated with the conservation of the square of the angular momentum:¹

$$I=\left(q-r\right)u_{1}^{2}+\left(r-p\right)u_{2}^{2}+\left(p-q\right)u_{3}^{2}. \tag{15}$$

In the general case, to find invariant characteristics of an S.H.T. one can use the symmetric tensor $c_{ik}$, formed from $\Gamma_{jk}^{i}$ by multiplication and double contraction:

$$c_{ik}=\Gamma_{i\mu}^{\lambda}\Gamma_{k\lambda}^{\mu}. \tag{16}$$

The existence of $c_{ik}$ together with $g_{ik}$ makes it possible to construct a natural coordinate system in which both of these matrices are reduced to diagonal form.

For a statistical description of an S.H.T. it is natural to use the general methods of statistical mechanics, introducing the phase density $\rho(u^{i},t)$ and its logarithm $\sigma=\log\rho$. By virtue of condition (6), the latter satisfies the well-known Liouville equation

$$\frac{\partial\sigma}{\partial t}+\dot{u}_{i}\frac{\partial\sigma}{\partial u_{i}}=0, \tag{17}$$

and a stationary distribution $\rho$ (respectively, $\sigma$) is an integral of motion. For any S.H.T. there is the stationary Boltzmann distribution

$$\sigma_{\Theta}\left(u_{i}\right)=g_{ik}u^{i}u^{k}/\Theta+\text{const}, \tag{18}$$

where $\Theta$ is the analogue of temperature. For the theory of turbulence only non-trivial stationary distributions are of interest, different from the Boltzmann distribution (which plays the role of "white noise"). In an S.H.T., non-trivial stationary Gaussian distributions, for which

$$\sigma\left(u_{i}\right)=\sigma_{\lambda\mu}u^{\lambda}u^{\mu}, \tag{19}$$

exist only if there is a quadratic integral of motion distinct from the energy. The simplest example, given by $S_3$, proves that such systems exist, but they are the exception rather than the rule. A second example of the same kind is the two-dimensional motion of an ideal incompressible fluid. Consider such a motion in a two-dimensional region $R$ bounded by the contour $\mathcal{L}$. The state of the system is determined by the stream function $\psi(x,y,t)$ with the boundary condition $\psi|_{\mathcal{L}}=0$, and the equations of motion take the form

$$\frac{\partial\psi}{\partial t}=\Delta^{-1}\left[\Delta\psi,\psi\right], \tag{20}$$

where $\Delta^{-1}$ is the Green operator of the Laplace equation and $\left[\chi,\psi\right]=\dfrac{\partial\chi}{\partial x}\dfrac{\partial\psi}{\partial y}-\dfrac{\partial\chi}{\partial y}\dfrac{\partial\psi}{\partial x}$.

There are two quadratic integrals of motion, the energy and the squared vorticity:

$$2E=\iint_{R}\left(\text{grad}\,\psi\right)^{2}dx\,dy, \tag{21}$$

$$I=\iint_{R}\left(\Delta\psi\right)^{2}dx\,dy. \tag{22}$$

In this case there is a two-parameter family of stationary Gaussian distributions. It is convenient to describe it explicitly in terms of the second moments of the spectral components $\psi^{i}$ of the field $\psi$, given by

$$\psi\left(x,y,t\right)=\psi^{\gamma}\left(t\right)\chi_{\gamma}\left(x,y\right),$$

where $\chi_{i}(x,y)$ are the solutions of

$$\Delta\chi_{i}=-k_{i}^{2}\chi_{i},\quad\chi_{i}|_{\mathcal{L}}=0,\quad\iint_{R}\chi_{i}^{2}\,dx\,dy=1. \tag{23}$$

For the characteristics of the field averaged with respect to the phase density (the average of a quantity $T(u_i)$ is denoted $\langle T\rangle$), it is not hard to obtain the following expressions:

$$\left\langle \psi^{i}\right\rangle =0,\qquad\left\langle \psi^{i}\psi^{j}\right\rangle =B_{\psi}^{ij}=\begin{cases}
0, & i\neq j,\\
E/k^{2}=C^{2}/k^{2}\left(1+L_{0}^{2}k^{2}\right), & i=j,
\end{cases} \tag{24}$$

where $C$ and $L_{0}$ are arbitrary constants; the first characterizes the intensity and the second the scale of the corresponding "two-dimensional turbulence".

In statistical hydromechanics [6] the method of moments, proposed in the well-known work of Friedmann and Keller [7], is widely used to describe the probability distribution in the corresponding mechanical systems. Instead of the phase density $\rho$ (which does not exist in the infinite-dimensional case), it uses the sequence of moments of various orders, i.e. the quantities $\langle u^{i}\rangle$, $B^{ij}=\langle u^{i}u^{j}\rangle$, $B^{ijk}=\langle u^{i}u^{j}u^{k}\rangle$, etc., which are symmetric tensors. For these statistical characteristics the equations of motion (4) yield an infinite chain of equations, known as the Friedmann–Keller equations. We write the first equations of this chain under the assumption that $\langle u^{i}\rangle=0$:

$$\Gamma_{\lambda\mu}^{i}B^{\lambda\mu}=0, \tag{25}$$

$$\dot{B}^{ij}=\Gamma_{\lambda\mu}^{i}B^{\lambda\mu j}+\Gamma_{\lambda\mu}^{j}B^{\lambda\mu i}, \tag{26}$$

$$\dot{B}^{ijk}=\Gamma_{\lambda\mu}^{i}B^{\lambda\mu jk}+\Gamma_{\lambda\mu}^{j}B^{\lambda\mu ki}+\Gamma_{\lambda\mu}^{k}B^{\lambda\mu ij}. \tag{27}$$

For an approximate solution of this system, M. D. Millionshchikov [8] proposed closing the equations above by an additional hypothesis, expressed by the relation

$$B^{ijkl}=B^{ij}B^{kl}+B^{ik}B^{jl}+B^{il}B^{jk}, \tag{28}$$

which holds exactly for the Gaussian distribution.

An investigation of the Friedmann–Keller chain constructed for an S.H.T. shows that any stationary solution of equations (25) and (27), obtained with the help of Millionshchikov's hypothesis (28), determines an exact solution of the whole chain in the form of the Gaussian distribution corresponding to the given second moments. In this case $B^{ijk}=0$, and all other odd moments vanish as well. The quadratic form $\sigma=\sigma_{\lambda\mu}u^{\lambda}u^{\mu}$, where the matrix $\sigma_{ij}$ is the inverse of $B^{ij}$ (i.e. $\sigma_{i\lambda}B^{\lambda k}=\delta_{i}^{k}$), is an exact integral of motion. It follows immediately that non-trivial solutions of the Friedmann–Keller chain for an S.H.T. exist only when, besides the energy integral, there is a second quadratic integral of motion.

*Institute of Atmospheric Physics, Academy of Sciences of the USSR. Received 11 October 1968.*

---

¹ An elegant proof that any S.H.T. with $n=3$ can be cast in the form (14), based on the matrix $A_{k}^{i}=\Gamma_{\lambda,k\mu}\epsilon^{i\lambda\mu}$ (where $\epsilon$ is the Levi-Civita tensor), is due to L. A. Dikii.

## References

1. A. M. Obukhov, "Ob integral'nykh invariantakh v sistemakh gidrodinamicheskogo tipa" [On integral invariants in systems of hydrodynamic type], *Doklady Akademii Nauk SSSR* **184**(2), 309–312 (1969). [Original on Math-Net.Ru](https://www.mathnet.ru/eng/dan34380).
2. L. D. Landau and E. M. Lifshitz, *Mechanics*, Course of Theoretical Physics, Vol. 1 (Russian edition: Nauka, 1965).
3. V. I. Arnold, "Sur la géométrie différentielle des groupes de Lie de dimension infinie et ses applications à l'hydrodynamique des fluides parfaits", *Annales de l'Institut Fourier* **16**(1), 319–361 (1966).
4. T. D. Lee, "On some statistical properties of hydrodynamical and magneto-hydrodynamical fields", *Quarterly of Applied Mathematics* **10**(1), 69–74 (1952).
5. P. D. Thompson, *Numerical Weather Analysis and Prediction*, Macmillan, New York (1961); Russian translation, Moscow (1962).
6. A. S. Monin and A. M. Yaglom, *Statistical Hydromechanics*, Part II, Nauka, Moscow (1967).
7. L. Keller and A. Friedmann, "Differentialgleichungen für die turbulente Bewegung einer kompressiblen Flüssigkeit", *Proc. First Internat. Congress Appl. Mech.*, Delft (1924).
8. M. D. Millionshchikov, *Izvestiya Akademii Nauk SSSR, Seriya Geograficheskaya i Geofizicheskaya* **5**(4–5) (1941).
