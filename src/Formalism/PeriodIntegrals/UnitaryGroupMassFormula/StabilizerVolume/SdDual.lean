module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

@[expose] public section

noncomputable section

namespace PI.VolStabS

namespace SdDualW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def latSub (a M : ℕ) : AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E) where
  carrier := latV b v
  zero_mem' := by
    simp only [latV, Set.mem_ofPred_eq]
    intro p i k
    simp
  add_mem' := by
    intro X Y hX hY
    simp only [latV, Set.mem_ofPred_eq] at hX hY ⊢
    intro p i k
    simpa [Pi.add_apply, map_add (f := _)] using add_mem (hX p i k) (hY p i k)
  neg_mem' := by
    intro X hX
    simp only [latV, Set.mem_ofPred_eq] at hX ⊢
    intro p i k
    simpa [map_neg] using neg_mem (hX p i k)

theorem crd_smul (s : Fv F v) (z : Fv F v ⊗[F] E) (k : Fin d) :
    crd b (Fv F v) (s • z) k = s * crd b (Fv F v) z k := by
  simp [crd]

theorem sigR_smul (σ : E →ₐ[F] E) (s : Fv F v) (z : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (s • z) = s • sigR (Fv F v) σ z := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem BR_smul_left (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : Fv F v)
    (X Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J (s • X) Y = s * BR (Fv F v) σ J X Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.smul_apply, sigR_smul, smul_mul_assoc, ← Finset.smul_sum,
    map_smul, smul_eq_mul, Finset.mul_sum]

theorem BR_add_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y Y' : Fin n → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X (Y + Y') = BR (Fv F v) σ J X Y + BR (Fv F v) σ J X Y' := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem BR_smul_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : Fv F v)
    (X Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X (s • Y) = s * BR (Fv F v) σ J X Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul,
    smul_eq_mul, Finset.mul_sum]

section Nondeg

variable [FiniteDimensional F E]

theorem trace_one_tmul (e : E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((1 : Fv F v) ⊗ₜ[F] e) =
      algebraMap F (Fv F v) (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k y => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]


include b in
theorem trace_nondeg [Algebra.IsSeparable F E] (z : Fv F v ⊗[F] E)
    (h : ∀ w, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w * z) = 0) : z = 0 := by
  apply PI.VolStabSW.SdDualW.trace_nondeg <;> assumption

end Nondeg

section Dual

variable [FiniteDimensional F E] (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)

def eT (q : Fin a × Fin M × Fin d) : Fin a → Fin M → Fv F v ⊗[F] E :=
  Pi.single q.1 (Pi.single q.2.1 ((1 : Fv F v) ⊗ₜ[F] b q.2.2))

theorem eT_mem (q : Fin a × Fin M × Fin d) : eT v b q ∈ latSub v b a M := by
  show ∀ p i l, (Algebra.TensorProduct.basis (Fv F v) b).repr (eT v b q p i) l ∈
    v.adicCompletionIntegers F
  intro p i l
  have hB : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b) k = (1 : Fv F v) ⊗ₜ[F] b k :=
    fun k => Algebra.TensorProduct.basis_apply _ _
  by_cases h1 : p = q.1
  · subst h1
    by_cases h2 : i = q.2.1
    · subst h2
      simp only [eT, Pi.single_eq_same]
      rw [← hB, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · simp [eT, h2]
  · simp [eT, h1]

theorem sum_eT (X : Fin a → Fin M → Fv F v ⊗[F] E) :
    X = ∑ q : Fin a × Fin M × Fin d, crd b (Fv F v) (X q.1 q.2.1) q.2.2 • eT v b q := by
  funext p i
  rw [Finset.sum_apply, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single p]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp only [eT, Pi.smul_apply, Pi.single_eq_same]
      exact eq_sum_crd b (Fv F v) (X p i)
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [eT, hj]
    · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [eT, Ne.symm hx]
  · simp

def brL (Y : Fin a → Fin M → Fv F v ⊗[F] E) : (Fin a → Fin M → Fv F v ⊗[F] E) →ₗ[Fv F v] Fv F v
    where
  toFun X := BR (Fv F v) σ J X Y
  map_add' X X' := by rw [add_comm X X', BR_add, add_comm]
  map_smul' s X := by rw [BR_smul_left]; rfl

theorem BR_expand (X Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X Y =
      ∑ q : Fin a × Fin M × Fin d, crd b (Fv F v) (X q.1 q.2.1) q.2.2 * BR (Fv F v) σ J (eT v b q) Y := by
  have h := congrArg (brL v σ J Y) (sum_eT v b X)

  simp only [map_sum, map_smul, smul_eq_mul] at h
  exact h

def phiL : (Fin a → Fin M → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin a × Fin M × Fin d → Fv F v) where
  toFun Y q := BR (Fv F v) σ J (eT v b q) Y
  map_add' Y Y' := by funext q; simp [BR_add_right]
  map_smul' s Y := by funext q; simp [BR_smul_right]

include b in
theorem bound_alt
    (hN : ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, (∀ X, BR (Fv F v) σ J X Y = 0) → Y = 0)
    (c : Fv F v) : ∃ K, IsCompact K ∧
      {y | ∀ x ∈ latSub v b a M, BR (Fv F v) σ J x y ∈
        (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))} ⊆ K := by
  apply PI.VolStabSW.SdDualW.bound_alt <;> assumption

include b in
theorem dualAt_alt
    (hN : ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, (∀ X, BR (Fv F v) σ J X Y = 0) → Y = 0) :
    DualAt v (BR (Fv F v) σ J (n := a)) := by
  apply PI.VolStabSW.SdDualW.dualAt_alt <;> assumption

end Dual

section NondegBR

variable [FiniteDimensional F E]

theorem nondeg_BR [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) (Y : Fin a → Fin M → Fv F v ⊗[F] E)
    (h : ∀ X, BR (Fv F v) σ J X Y = 0) : Y = 0 := by
  apply PI.VolStabSW.SdDualW.nondeg_BR <;> assumption

end NondegBR

section Herm

variable [FiniteDimensional F E]

def latA : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := {z | ∀ k, crd b (Fv F v) z k ∈ v.adicCompletionIntegers F}
  zero_mem' := by intro k; simp [crd]
  add_mem' := by
    intro x y hx hy k
    simpa [crd, map_add (f := _)] using add_mem (hx k) (hy k)
  neg_mem' := by
    intro x hx k
    simpa [crd, map_neg] using neg_mem (hx k)

theorem isOpen_latA : IsOpen (latA v b : Set (Fv F v ⊗[F] E)) := by
  have e : (latA v b : Set (Fv F v ⊗[F] E)) = ⋂ k, (fun z => crd b (Fv F v) z k) ⁻¹'
      (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext z; simp [latA]
  rw [e]
  exact isOpen_iInter_of_finite fun k =>
    (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).preimage (continuous_crd b (Fv F v) k)

theorem isCompact_latA : IsCompact (latA v b : Set (Fv F v ⊗[F] E)) := by
  have e : (latA v b : Set (Fv F v ⊗[F] E)) =
      (fun Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E => Y 0 0) '' latV (M := 1) (n := 1) b v := by
    ext z
    constructor
    · intro hz
      exact ⟨fun _ _ => z, fun p i k => hz k, rfl⟩
    · rintro ⟨Y, hY, rfl⟩ k
      exact hY 0 0 k
  rw [e]
  exact (isCompact_latV b v 1 1).image ((continuous_apply 0).comp (continuous_apply 0))

def latS (σ : E →ₐ[F] E) : AddSubgroup (Fv F v ⊗[F] E) :=
  latA v b ⊔ (latA v b).map (sigR (Fv F v) σ).toAddMonoidHom

theorem mem_latS (σ : E →ₐ[F] E) (z : Fv F v ⊗[F] E) :
    z ∈ latS v b σ ↔ ∃ x ∈ latA v b, ∃ y ∈ latA v b, x + sigR (Fv F v) σ y = z := by
  simp only [latS, AddSubgroup.mem_sup, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, _, ⟨y, hy, rfl⟩, rfl⟩

theorem isCompact_latS (σ : E →ₐ[F] E) : IsCompact (latS v b σ : Set (Fv F v ⊗[F] E)) := by
  have e : (latS v b σ : Set (Fv F v ⊗[F] E)) =
      (fun p : (Fv F v ⊗[F] E) × (Fv F v ⊗[F] E) => p.1 + sigR (Fv F v) σ p.2) ''
        ((latA v b : Set (Fv F v ⊗[F] E)) ×ˢ (latA v b : Set (Fv F v ⊗[F] E))) := by
    ext z
    rw [SetLike.mem_coe, mem_latS]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      exact ⟨x, hx, y, hy, rfl⟩
  rw [e]
  have := locallyCompact_Fv F v
  exact ((isCompact_latA v b).prod (isCompact_latA v b)).image
    (continuous_fst.add ((continuous_sigR (Fv F v) σ).comp continuous_snd))

theorem isOpen_latS (σ : E →ₐ[F] E) : IsOpen (latS v b σ : Set (Fv F v ⊗[F] E)) :=
  AddSubgroup.isOpen_mono le_sup_left (isOpen_latA v b)

theorem smul_mem_latA {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ latA v b) : s • x ∈ latA v b := by
  intro k
  rw [crd_smul]
  exact mul_mem hs (hx k)

theorem smul_mem_latS (σ : E →ₐ[F] E) {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {z : Fv F v ⊗[F] E} (hz : z ∈ latS v b σ) : s • z ∈ latS v b σ := by
  rw [mem_latS] at hz ⊢
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  exact ⟨s • x, smul_mem_latA v b hs hx, s • y, smul_mem_latA v b hs hy, by
    rw [smul_add, sigR_smul]⟩

theorem trace_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (w : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ w) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w := by
  let B := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
  have hB : ∀ k, B k = (1 : Fv F v) ⊗ₜ[F] (Module.finBasis F E) k := fun k =>
    Algebra.TensorProduct.basis_apply _ _
  let eσ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ
    ⟨σ.toRingHom.injective, fun x => ⟨σ x, hσ x⟩⟩
  have htr : ∀ e : E, Algebra.trace F E (σ e) = Algebra.trace F E e := fun e =>
    Algebra.trace_eq_of_algEquiv eσ e
  conv_lhs => rw [← B.sum_repr w]
  conv_rhs => rw [← B.sum_repr w]

  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sigR_smul, map_smul, map_smul, hB]
  have : sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] (Module.finBasis F E) k) =
      (1 : Fv F v) ⊗ₜ[F] σ ((Module.finBasis F E) k) := by simp [sigR]
  rw [this, trace_one_tmul, trace_one_tmul, htr]

def latH (σ : E →ₐ[F] E) (a : ℕ) : AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ p q, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q ∈ latS v b σ}
  zero_mem' := by intro p q; simp
  add_mem' := by
    intro S T hS hT p q
    simpa using add_mem (hS p q) (hT p q)
  neg_mem' := by
    intro S hS p q
    simpa using neg_mem (hS p q)

theorem latH_eq (σ : E →ₐ[F] E) (a : ℕ) :
    (latH v b σ a : Set (HermR (Fv F v) σ a)) = Subtype.val ⁻¹'
      ((Set.univ.pi fun _ => Set.univ.pi fun _ => (latS v b σ : Set (Fv F v ⊗[F] E))) :
        Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) := by
  ext S
  exact ⟨fun h p _ q _ => h p q, fun h p q => h p (Set.mem_univ _) q (Set.mem_univ _)⟩

def iota (σ : E →ₐ[F] E) {a : ℕ} (X : Fin a → Fin a → Fv F v ⊗[F] E) :
    Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) :=
  fun p q => sigR (Fv F v) σ (X p q) + X q p

theorem iota_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {a : ℕ}
    (X : Fin a → Fin a → Fv F v ⊗[F] E) : iota v σ X ∈ HermR (Fv F v) σ a := by
  intro p q
  simp only [iota, map_add (f := _), sigR_invol (Fv F v) σ hσ]
  exact add_comm _ _

theorem pairHerm_iota (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {a : ℕ}
    (X : Fin a → Fin a → Fv F v ⊗[F] E) (T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a ⟨iota v σ X, iota_mem v σ hσ X⟩ T =
      BR (Fv F v) σ (1 : Matrix (Fin a) (Fin a) E) X
        (fun p i => (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i p) := by
  apply PI.VolStabSW.SdDualW.pairHerm_iota <;> assumption

include b in
theorem dualAt_H [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) :
    DualAt v (pairHerm (Fv F v) σ a) := by
  apply PI.VolStabSW.SdDualW.dualAt_H <;> assumption

end Herm

end SdDualW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW

def DualHV : Prop := InCtx fun F E _ _ _ _ _ σ _M _J a _X0 _hT =>
  ∀ v : HeightOneSpectrum (𝓞 F), DualAt v (pairHerm (Fv F v) σ a)

theorem dualLatV_of (hH : DualHV) : DualLatV := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  refine ⟨?_, hH F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v⟩
  exact SdDualW.dualAt_alt v (Module.finBasis F E) σ J
    (fun Y hY => SdDualW.nondeg_BR v σ hσ J hJ.2 Y hY)

theorem dualHV_holds : DualHV := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact SdDualW.dualAt_H v (Module.finBasis F E) σ (sigma_invol σ hCM.2.2.2) a

theorem dualLatV_holds : DualLatV := dualLatV_of dualHV_holds

theorem sdUniq_of_inf (hI : SdTestInf) : SdUniq := sdUniq_of_dual hI dualLatV_holds

end PI.VolStabS
