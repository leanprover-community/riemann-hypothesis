module

public import Lib.SiegelWeil.Tower.TestVector
public import Lib.SiegelWeil.Tower.LineGaussSums
public import Lib.Weil.DualPair.ThetaIntegrals
import Lib.Weil.Construction.CanonicalTheta
import New.Determinant.Exchange.RemovingPlanes

/-!
# Vanishing of theta integrals descends along hyperbolic planes

If the theta integral of `(W ⊕ H, V ⊕ H)` vanishes on the multiples of the determinant vectors and
on all standard data, so does that of `(W, V)`, provided the rank of `W ⊕ H` is `2 (k + q)`, with
`q` its number of negative signs and `k ≤ min μ` a natural number. The constant term along the new
isotropic line is a non-zero multiple of the theta integral of `(W, V)` at a cone integral, formed
on the side of the summation formula on the line that the sign of `rk V - rk W / 2` selects, and
every multiple of a determinant vector of `(W, V)` is such a cone integral of one of
`(W ⊕ H, V ⊕ H)` (`exists_integral_coneIntegrand_detVector`). Only values of the `L`-function at
points `≥ 1` occur.
The file also computes the theta kernels of pairs in which one space is `0`, where the determinant
vector is the vacuum.

Notions from other files:
* `thetaLarge W V 𝔠 v Φ`: the theta integral over `[U(V)]` of `v ⊗ Φ`, a function on `G E s`;
* `stdRowDatum σ χ y`: the finite datum `x ↦ χ⁻¹ (det (y; x))`, supported where the square matrix
  `(y; x)`, with rows ordered by `σ`, is invertible and integral;
* `SplitTameChar E μ`: a tame character of weight `μ`, ramified at a finite set of split places;
* `negCount s`: the number of signs `-1` among `s`;
* `detVector s t k m F`: the determinant vector, the Fock vector of the polynomial with value the
  conjugate of `∏ w, det₊ (u₊ F w) ^ m w * det₋ (u₊ F w) ^ (m w + 2 k)` at `u`.

## Relation to the literature

See `New.Determinant.Exchange.TheoremForPartners` for related work.
-/

@[expose] public section

noncomputable section

namespace New.Exchange

open MeasureTheory Fintype Fock Space Set
open NumberField (InfinitePlace)

variable {E : Type} [Field E] [CMType E]

/-- For the tame part `χ` of a split tame character `𝔠`, the standard datum
`stdColDatum 𝔠.semilocalChar 1`, which sends an integral matrix `y` with unit determinant to
`χ⁻¹ (det y)` and all other matrices to zero, has the value `1` at the identity matrix. -/
lemma stdColDatum_one_one {n : Type} [Fintype n] [DecidableEq n] {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) :
    stdColDatum 𝔠.semilocalChar 1 (1 : Matrix n n (LocProd 𝔠.ramifiedPlaces)) = 1 := by
  simp [stdColDatum, IsIntMatrix.one, invOnUnits, IsIntegralUnit]

variable [WeilData E]

/-- For a space `W` of rank zero, the operator `W.schrodingerOp 𝔠.ramifiedPlaces Φ` (a combination
of Heisenberg operators at the ramified places `𝔠.ramifiedPlaces` that represents the function `Φ`
of finite adelic vectors) sends the vacuum `W.vacElem` to `Φ 0` times the vacuum. -/
lemma schrodingerOp_vacElem_of_isEmpty {n : Type} [Fintype n] [DecidableEq n] [IsEmpty n]
    {s : n → ℤˣ} (W : Space E n s) {μ : InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ)
    (Φ : (n → 𝔸f E) → ℂ) :
    W.schrodingerOp 𝔠.ramifiedPlaces Φ W.vacElem = Φ 0 • W.vacElem := by
  -- In rank zero `Φ` is a constant, so it is a multiple of the indicator function `boxIndicator`.
  have hΦ : Φ = Φ 0 • boxIndicator n 𝔠.ramifiedPlaces := by
    funext x
    simp [Subsingleton.eq_zero x, boxIndicator_apply]
  conv_lhs => rw [hΦ, map_smul, _root_.smul_apply,
    schrodingerOp_boxIndicator 𝔠.readsAt.disjoint_star, projOn_vacElem]

section RankZero

open Finset

variable {n : Type} [Fintype n] [DecidableEq n] {s : n → ℤˣ}

/-- For a hermitian space `W` of rank zero (`n` empty) over a CM field `E` with Weil data, the theta
functional `W.θ` takes the value `1` on the vacuum `W.vacElem` (the Gaussian times twisted lattice
indicator, as an element of 𝒮(W)). -/
lemma theta_vacElem_of_isEmpty (W : Space E n s) [IsEmpty n] : W.θ W.vacElem = 1 := by
  rw [theta_apply, vacElem_apply_eq_prod_lineTheta (fun _ ↦ Subsingleton.elim _ _), univ_eq_empty,
    Finset.prod_empty]

/-- Take the datum with the Fock vector `x` as archimedean part and the function `Φ` at the ramified
places of `𝔠`. The theta kernel of the pair `(W, 0)`, twisted by characters `α`, `β` of `[U(1)]`,
at this datum and at adelic unitary elements `(g, h)` is `β (det g)⁻¹ * Φ 0` times the theta
functional of the space `Hom(W, 0)` at the image of the vacuum under the integrated operator of
`x`. -/
lemma pairTheta_target_zero (W : Space E n s) (α β : AutChar E) {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) (x : PairFock E s (1 : Empty → ℤˣ))
    (Φ : Matrix Empty n (LocProd 𝔠.ramifiedPlaces) → ℂ) (g : G E s) (h : G E (1 : Empty → ℤˣ)) :
    pairTheta W (stdSpace E Empty) α β (localDatum W (stdSpace E Empty) x Φ 𝔠.readsAt) (g, h) =
      (β.val g.det : ℂ)⁻¹ * Φ 0 * (W.hom (stdSpace E Empty)).θ
        ((W.hom (stdSpace E Empty)).integrated x (W.hom (stdSpace E Empty)).vacElem) := by
  -- The space `H` of homomorphisms is `0`: the group acts trivially and `Φ` is read at `0`.
  set H : Space E (Empty × n) (homSigns s 1) := W.hom (stdSpace E Empty)
  have h_datum : localDatum W (stdSpace E Empty) x Φ 𝔠.readsAt =
      H.integrated x (Φ 0 • H.vacElem) := by
    rw [localDatum, schrodingerOp_vacElem_of_isEmpty, congrArg Φ (Subsingleton.eq_zero _)]
  rw [pairTheta, pairWeil_apply, Subsingleton.eq_one (G.onHom (g, h)), h_datum,
    Subsingleton.eq_one h]
  simp [H, mul_assoc]

/-- The theta kernel of the pair `(0, W)` twisted by `α` and `β`, at the datum with the vacuum as
archimedean part and the function `Ψ` at the ramified places of `𝔠`, is `α (det g) * Ψ 0`. -/
lemma pairTheta_source_zero (W : Space E n s) (α β : AutChar E) {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) (Ψ : Matrix n Empty (LocProd 𝔠.ramifiedPlaces) → ℂ)
    (h : G E (1 : Empty → ℤˣ)) (g : G E s) :
    pairTheta (stdSpace E Empty) W α β
        (localDatum (stdSpace E Empty) W vacVector Ψ 𝔠.readsAt) (h, g) =
      α.val g.det * Ψ 0 := by
  -- The space `H` of homomorphisms is `0`: the group acts trivially and `Ψ` is read at `0`.
  let H : Space E (n × Empty) (homSigns 1 s) := (stdSpace E Empty).hom W
  have h_datum : localDatum (stdSpace E Empty) W vacVector Ψ 𝔠.readsAt = Ψ 0 • H.vacElem := by
    rw [localDatum, schrodingerOp_vacElem_of_isEmpty, congrArg Ψ (Subsingleton.eq_zero _)]
    simp only [H, map_smul, projReal_eq_self_of_mem_finitePart, vacElem_mem_finitePart]
  rw [pairTheta, pairWeil_apply, Subsingleton.eq_one (G.onHom (h, g)), h_datum,
    Subsingleton.eq_one h, map_one, one_apply_eq_self, map_smul, map_smul,
    theta_vacElem_of_isEmpty H]
  simp

/-- For the pair `(W, 0)`, the theta integral at `1` of the datum with the vacuum as archimedean
part and the function `Φ` at the ramified places of `𝔠` is the volume of `[U(0)]`, the domain of
integration, times `Φ 0`. -/
lemma thetaLarge_stdSpace_empty_vacVector_one (W : Space E n s) {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) (Φ : Matrix Empty n (LocProd 𝔠.ramifiedPlaces) → ℂ) :
    thetaLarge W (stdSpace E Empty) 𝔠 vacVector Φ 1 =
      (stdSpace E Empty).quotMeasure.real univ * Φ 0 := by
  have h_kernel (h : G E (1 : Empty → ℤˣ)) :
      pairTheta W (stdSpace E Empty) (rankTwist 𝔠.character⁻¹ n) (rankTwist 𝔠.character⁻¹ n)
        (localDatum W (stdSpace E Empty) vacVector Φ 𝔠.readsAt) (1, h) = Φ 0 := by
    simp only [pairTheta_target_zero, map_one, Circle.coe_one, inv_one, one_mul,
      projReal_eq_self_of_mem_finitePart, vacElem_mem_finitePart, theta_vacElem_of_isEmpty, mul_one]
  simp only [thetaLarge, thetaIntegral, h_kernel, integral_const, Complex.real_smul]

end RankZero

variable {n n' r r' b : Type} [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] [Fintype r']
  [DecidableEq r'] [Fintype b] [DecidableEq b] {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ}
  {t' : r' → ℤˣ} {μ : InfinitePlace E → ℤ} {𝔠 : SplitTameChar E μ}

variable (𝔠) in
/-- Let `W` and `V` be hermitian spaces over `E` with bases indexed by `n` and `r` and with signs
`s` and `t` at the infinite places. The theta integral of `(W, V)` for the split tame character `𝔠`,
a function on the adelic unitary group `G E s` of `W`, vanishes on all Schwartz vectors `v` (all
Fock moments finite) of the Fock space `PairFock E s t` of `Hom(W, V)` and all standard data
`stdRowDatum σ 𝔠.semilocalChar y`. Here `y` is any integral `b × n` matrix over the product of the
completions at the ramified places `𝔠.ramifiedPlaces`, and `σ` orders the rows of `y` and of an
`r × n` matrix into a square matrix. -/
def ThetaLargeVanishes (W : Space E n s) (V : Space E r t) (σ : b ⊕ r ≃ n) : Prop :=
  ∀ v : PairFock E s t, IsSchwartzVector v →
    ∀ y : Matrix b n (LocProd 𝔠.ramifiedPlaces), IsIntMatrix SemilocalField.O y →
      ∀ g : G E s, thetaLarge W V 𝔠 v (stdRowDatum σ 𝔠.semilocalChar y) g = 0

variable (𝔠) in
/-- The theta integral of `(W, V)` for the split tame character `𝔠` of weight `μ` vanishes, at
every point of the adelic unitary group of `W`, on all multiples of the determinant vectors
`detVector s t k m F` with `m w = μ w - k`, and on all standard data
`stdRowDatum σ 𝔠.semilocalChar y` with `y` integral at the ramified places of `𝔠`. -/
def ThetaLargeVanishesOnDetVectors (k : ℕ) (W : Space E n s) (V : Space E r t) (σ : b ⊕ r ≃ n) :
    Prop :=
  ∀ (c : ℂ) (F : InfinitePlace E → Matrix n r ℂ) (y : Matrix b n (LocProd 𝔠.ramifiedPlaces)),
    IsIntMatrix SemilocalField.O y → ∀ g : G E s,
      thetaLarge W V 𝔠 (c • detVector s t k (fun w ↦ (μ w - k).toNat) F)
        (stdRowDatum σ 𝔠.semilocalChar y) g = 0

omit [Fintype b] [DecidableEq b] in
/-- A theta integral that vanishes on all Schwartz vectors vanishes on the multiples of the
determinant vectors. -/
lemma ThetaLargeVanishes.onDetVectors {W : Space E n s} {V : Space E r t} {σ : b ⊕ r ≃ n}
    (h_zero : ThetaLargeVanishes 𝔠 W V σ) (k : ℕ) : ThetaLargeVanishesOnDetVectors 𝔠 k W V σ :=
  fun c F ↦ h_zero _ (isSchwartzVector_smul_detVector c k _ F)

omit [Fintype b] [DecidableEq b] in
/-- Let `W`, `W₁` be hermitian spaces with the same signs `s`, and `V`, `V₁` with the same signs
`t`. If, for the split tame character `𝔠`, the theta integral of `(W, V)` at every point of the
unitary group of `W` vanishes on all multiples of determinant vectors and all standard data, so
does that of `(W₁, V₁)`. -/
lemma ThetaLargeVanishesOnDetVectors.congr_spaces {k : ℕ} {W : Space E n s} {V : Space E r t}
    {σ : b ⊕ r ≃ n} (h_zero : ThetaLargeVanishesOnDetVectors 𝔠 k W V σ) (W₁ : Space E n s)
    (V₁ : Space E r t) : ThetaLargeVanishesOnDetVectors 𝔠 k W₁ V₁ σ := by
  obtain ⟨γ, h_transport⟩ := exists_thetaLarge_thetaSmall_eq_circle_mul W W₁ V V₁ V V₁
  -- The integral of `(W₁, V₁)` at `g` is `u` times that of `(W, V)` at `γ * g`.
  obtain ⟨u, h_eq_mul⟩ := (h_transport 𝔠).left
  intro c F y hy g
  rw [h_eq_mul, h_zero c F y hy, mul_zero]

/-- Descent along one hyperbolic plane `H`. Let `A` and `X` be adapted splittings (orthonormal at
the infinite and integral at the finite places) `W' = W ⊕ H` and `V' = V ⊕ H` of hermitian spaces.
Let `W` be of even rank and `W'` of rank `2 (k + q')`, where `q'` is its number of negative signs
and `k ≤ μ w` at every infinite place `w`, for the weight `μ` of the split tame character `𝔠`.

If at every point of the unitary group of `W'` the theta integral of `(W', V')` vanishes on all
multiples of determinant vectors and all data `stdRowDatum σ' 𝔠.semilocalChar y'`, then at every
point of the unitary group of `W` that of `(W, V)` vanishes on all multiples of determinant vectors
and all data `stdRowDatum σ 𝔠.semilocalChar y`. Here `y'` and `y` are arbitrary integral matrices
at the ramified places of `𝔠`, with rows indexed by `b` and columns by the bases of `W'` and `W`;
the orderings `σ` and `σ'` of these rows and those indexed by the basis of `V`, respectively `V'`,
into a square matrix are arbitrary. -/
theorem ThetaLargeVanishesOnDetVectors.of_add_plane {k : ℕ} {W : Space E n s} {W' : Space E n' s'}
    {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit) (X : V'.Splitting V Unit)
    [IsBaseAdapted A] [IsBaseAdapted X] (σ : b ⊕ r ≃ n) {σ' : b ⊕ r' ≃ n'} (hn_even : 2 ∣ card n)
    (hk_le : ∀ w : InfinitePlace E, k ≤ μ w) (h_card : card n' = 2 * (k + negCount s'))
    (h_zero : ThetaLargeVanishesOnDetVectors 𝔠 k W' V' σ') :
    ThetaLargeVanishesOnDetVectors 𝔠 k W V σ := by
  intro c F y hy g
  have hμ (w : InfinitePlace E) : μ w = k + ((μ w - k).toNat : ℕ) := by
    have h_le := hk_le w
    omega
  -- The sign of `rk V - rk W / 2` decides on which side of the summation formula on the line the
  -- cone is formed.
  obtain ⟨β, z, hz⟩ : ∃ (β : Bool) (z : ℕ),
      ((card r - card n / 2 : ℤ) + 1 : ℝ) = cond β (z + 1 : ℝ) (1 - (z + 1)) := by
    obtain ⟨z, hz | hz⟩ : ∃ z : ℕ,
        (card r - card n / 2 : ℤ) = z ∨ (card r - card n / 2 : ℤ) = -(z + 1) := by
      cases (card r - card n / 2 : ℤ) <;> simp [Int.negSucc_eq]
    · exact ⟨true, z, by simp [hz]⟩
    · exact ⟨false, z, by simp [hz]⟩
  -- The constant term of the theta integral of `(W', V')` is `γ ≠ 0` times the theta integral of
  -- `(W, V)` at the cone integral, and `c • detVector s t k m F` is such a cone integral.
  obtain ⟨C, hC_pos, h_plane⟩ := exists_planeConstantTerm_eq_thetaLarge A X σ' σ hn_even μ β hz
  obtain ⟨γ, hγ, h_term⟩ := h_plane 𝔠
  obtain ⟨c', h_cone⟩ := exists_integral_coneIntegrand_detVector A X β (z := (z : ℝ) + 1)
    (by positivity) h_card (fun w ↦ (μ w - k).toNat) hμ F c
  have h_const := h_term _ (isSchwartzVector_smul_detVector c' k (fun w ↦ (μ w - k).toNat)
    (liftFrame A X F)) y hy 1 g (.inl rfl)
  rw [h_cone] at h_const
  -- The constant term is that of a function that vanishes.
  have h_int := hy.mul (adaptedFrame 𝔠.readsAt A).blockRelations.isIntMatrix_dualI
  have h_left : planeConstantTerm 𝔠 V' A σ'
      (c' • detVector s' t' k (fun w ↦ (μ w - k).toNat) (liftFrame A X F)) y 1 g = 0 := by
    simp only [planeConstantTerm, h_zero c' (liftFrame A X F) _ h_int, integral_zero]
  have hγ_ne : γ ≠ 0 :=
    norm_pos_iff.1 ((mul_pos hC_pos (lSharp_pos 𝔠 (by simp))).trans_eq hγ.symm)
  exact (mul_eq_zero.1 (h_const.symm.trans h_left)).resolve_left hγ_ne

/-- Descent along any positive number `j` of hyperbolic planes `H`. Let the hermitian space `W'`
have the rank and number of negative signs of `W ⊕ H ^ j`, and let `V'` have the number of negative
signs of `V ⊕ H ^ j`; its rank is then that of `V ⊕ H ^ j` too, by `σ` and `σ'`. Let `W` have rank
`2 (k + q)`, where `q` is its number of negative signs, `k ≤ μ w` at every infinite place `w` and
`μ` is the weight of the split tame character `𝔠`.

If at every point of the unitary group of `W'` the theta integral of `(W', V')` vanishes on all
multiples of determinant vectors and all data `stdRowDatum σ' 𝔠.semilocalChar y'`, then at every
point of the unitary group of `W` that of `(W, V)` vanishes on all multiples of determinant vectors
and all data `stdRowDatum σ 𝔠.semilocalChar y`. Integrality at the ramified places of `𝔠` is the
only condition on the matrices `y'` and `y`; their rows are indexed by `b`, and `σ`, `σ'` order
these rows and those indexed by the basis of `V`, respectively `V'`, into a square matrix. -/
theorem ThetaLargeVanishesOnDetVectors.of_add_planes {k : ℕ} {W' : Space E n' s'}
    {V' : Space E r' t'} {σ' : b ⊕ r' ≃ n'} (h_zero : ThetaLargeVanishesOnDetVectors 𝔠 k W' V' σ')
    (hk_le : ∀ w : InfinitePlace E, k ≤ μ w) {j : ℕ} (hj : 1 ≤ j) (W : Space E n s)
    (V : Space E r t) (σ : b ⊕ r ≃ n) (h_card : card n = 2 * (k + negCount s))
    (h_rank : card n' = card n + 2 * j) (h_negCount_W : negCount s' = j + negCount s)
    (h_negCount_V : negCount t' = j + negCount t) : ThetaLargeVanishesOnDetVectors 𝔠 k W V σ := by
  induction j, hj using Nat.le_induction generalizing n r with
  | base =>
    have h_card_W : card b + card r = card n := card_sum.symm.trans (card_congr σ)
    have h_card_W' : card b + card r' = card n' := card_sum.symm.trans (card_congr σ')
    obtain ⟨W₁, A, _⟩ := exists_isBaseAdapted Unit W s' (by simp [h_rank]) (by simp [h_negCount_W])
    have h_rank_V : card r' = card r + 2 := by omega
    obtain ⟨V₁, X, _⟩ :=
      exists_isBaseAdapted Unit V t' (by simp [h_rank_V]) (by simp [h_negCount_V])
    exact (h_zero.congr_spaces W₁ V₁).of_add_plane A X σ ⟨_, h_card⟩ hk_le (by omega)
  | succ j _ ih =>
    -- Descend to `(H ⊕ W, H ⊕ V)`, then remove the last plane.
    have h_card_σ : card (b ⊕ r) = card n := card_congr σ
    let τ : b ⊕ (Unit ⊕ Unit) ⊕ r ≃ (Unit ⊕ Unit) ⊕ n :=
      equivOfCardEq (by simp +arith [← h_card_σ])
    -- One plane raises each rank by two and each number of negative signs by one.
    have h_card_above : card ((Unit ⊕ Unit) ⊕ n) =
        2 * (k + negCount (Sum.elim (hyperbolicSigns Unit) s)) := by simp +arith [h_card, two_mul]
    have h_above := ih (hyperbolicSum Unit W) (hyperbolicSum Unit V) τ h_card_above
      (by simp +arith [h_rank, two_mul]) (by simp +arith [h_negCount_W])
      (by simp +arith [h_negCount_V])
    exact h_above.of_add_plane (removePlanes Unit W) (removePlanes Unit V) σ ⟨_, h_card⟩ hk_le
      h_card_above

end New.Exchange
