module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

theorem mem_forms {f : F.G → W} : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W ↔
    ∀ (γ : F.Γ) (g : F.G) (κ : F.K), f ((γ : F.G) * g * κ) = jK κ⁻¹ • f g := Iff.rfl


variable {F lam jK} in
theorem jK_eq (hJ : F.IsJ lam jK) {κ κ' : F.K} (h1 : F.kap κ' = F.kap κ) (h2 : F.chi κ' = F.chi κ) : jK κ' = jK κ := by
  rw [hJ κ', hJ κ, h1, h2]

variable {F lam jK} in
theorem jK_inv_congr {κ κ' : F.K} (h : jK κ' = jK κ) : jK κ'⁻¹ = jK κ⁻¹ := by
  have e1 : jK κ'⁻¹ * jK κ' = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e2 : jK κ * jK κ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc jK κ'⁻¹ = jK κ'⁻¹ * (jK κ * jK κ⁻¹) := by rw [e2, mul_one]
    _ = (jK κ'⁻¹ * jK κ') * jK κ⁻¹ := by rw [h, mul_assoc]
    _ = jK κ⁻¹ := by rw [e1, one_mul]

theorem grpA_one : grpA F.O N lam 1 = 1 := Subtype.ext (by simp [grpA, grp])


variable {F lam jK} in
theorem jK_inv_of_triv (hJ : F.IsJ lam jK) {κ : F.K} (h1 : F.kap κ = 1) (h2 : F.chi κ = 1) : jK κ⁻¹ = 1 := by
  have : jK κ = jK 1 := by rw [hJ κ, h1, h2, map_one, grpA_one]; simp
  rw [jK_inv_congr this, inv_one, map_one]

def heckeFn (i : F.I) (f : F.G → W) : F.G → W := fun g => F.cst i • ∑ s ∈ F.tr i, f (g * s)

variable {F lam jK W}

theorem heckeFn_mem (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) {f : F.G → W}
    (hf : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W) : heckeFn F W i f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W := by
  rw [mem_forms] at hf ⊢
  intro γ g κ
  obtain ⟨σ, hσ⟩ := hOk.perm i κ
  have key : ∀ s : F.tr i, f ((γ : F.G) * g * κ * s) = jK κ⁻¹ • f (g * (σ s : F.G)) := by
    intro s
    obtain ⟨κ', h1, h2, h3⟩ := hσ s
    have e : (γ : F.G) * g * κ * s = γ * (g * σ s) * κ' := by
      rw [mul_assoc ((γ : F.G) * g) (κ : F.G) (s : F.G), h1]; simp only [mul_assoc]
    rw [e, hf γ (g * σ s) κ', jK_inv_congr (jK_eq hJ h2 h3)]
  simp only [heckeFn]
  rw [← Finset.sum_coe_sort (F.tr i), ← Finset.sum_coe_sort (F.tr i)]
  simp_rw [key]
  rw [← Finset.smul_sum, Equiv.sum_comp σ (fun s : F.tr i => f (g * (s : F.G))), smul_comm]

theorem heckeFn_comm (hOk : F.Ok) (hJ : F.IsJ lam jK) (i j : F.I) {f : F.G → W}
    (hf : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W) :
    heckeFn F W i (heckeFn F W j f) = heckeFn F W j (heckeFn F W i f) := by
  rw [mem_forms] at hf
  funext g
  obtain ⟨σ, hσ⟩ := hOk.comm i j
  have key : ∀ x : F.tr i × F.tr j, f (g * x.1 * x.2) = f (g * (σ x).1 * (σ x).2) := by
    intro x
    obtain ⟨hK, h1, h2⟩ := hσ x
    have e : g * x.1 * x.2 = ((1 : F.Γ) : F.G) * (g * (σ x).1 * (σ x).2) * (⟨_, hK⟩ : F.K) := by
      simp only [OneMemClass.coe_one, one_mul, mul_assoc, mul_inv_cancel_left]
    rw [e, hf, jK_inv_of_triv hJ h1 h2, one_smul]
  have hsum : ∀ (a b : F.I), heckeFn F W a (heckeFn F W b f) g =
      F.cst a • F.cst b • ∑ x : F.tr a × F.tr b, f (g * x.1 * x.2) := by
    intro a b
    simp only [heckeFn, Fintype.sum_prod_type, Finset.smul_sum]
    rw [← Finset.sum_coe_sort (F.tr a)]
    refine Fintype.sum_congr _ _ fun s => ?_
    rw [← Finset.sum_coe_sort (F.tr b)]
  rw [hsum, hsum, smul_comm (F.cst i) (F.cst j)]
  congr 2
  rw [Fintype.sum_congr _ _ key, Equiv.sum_comp σ (fun y : F.tr j × F.tr i => f (g * y.1 * y.2))]

end GlobalTheory.ExpFrame.HeckeMod

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
  {jK : F.K →* alg F.O N lam} {W : Type} [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

def op (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) :
    Module.End F.O (Forms F.O (A := alg F.O N lam) F.Γ jK W) where
  toFun f := ⟨heckeFn F W i f, heckeFn_mem hOk hJ i f.2⟩
  map_add' f f' := by
    ext g
    simp [heckeFn, Finset.sum_add_distrib, smul_add]
  map_smul' c f := by
    ext g
    simp [heckeFn, Finset.smul_sum, smul_comm (F.cst i) c]

theorem op_comm (hOk : F.Ok) (hJ : F.IsJ lam jK) (i j : F.I) :
    (op (W := W) hOk hJ i) * op hOk hJ j = op hOk hJ j * op hOk hJ i := by
  ext f : 1
  exact Subtype.ext (heckeFn_comm hOk hJ i j f.2)

end GlobalTheory.ExpFrame.HeckeMod

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
  {jK : F.K →* alg F.O N lam} {W : Type} [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

open scoped IsMulCommutative in
def heckeAlg (hOk : F.Ok) (hJ : F.IsJ lam jK) : F.T →ₐ[F.O] Module.End F.O (Forms F.O (A := alg F.O N lam) F.Γ jK W) :=
  letI : IsMulCommutative (Algebra.adjoin F.O (Set.range (op (W := W) hOk hJ))) :=
    Algebra.isMulCommutative_adjoin F.O (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact op_comm hOk hJ i j)
  (Algebra.adjoin F.O (Set.range (op (W := W) hOk hJ))).val.comp
    (MvPolynomial.aeval fun i => ⟨op hOk hJ i, Algebra.subset_adjoin ⟨i, rfl⟩⟩)

theorem heckeAlg_X (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) : heckeAlg (W := W) hOk hJ (X i) = op hOk hJ i := by
  simp [heckeAlg]

theorem hecke_module : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam), F.Ok → F.IsJ lam jK → ∀ (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W], ∃ (_ : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)) (_ : IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)), F.IsHecke lam jK W := by
  intro l _ ι _ _ N F lam jK hOk hJ W _ _ _ _
  letI inst : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W) := Module.compHom _ (heckeAlg (W := W) hOk hJ).toRingHom
  refine ⟨inst, ⟨fun c t f => ?_⟩, fun c f => ?_, fun i f g => ?_⟩
  · change heckeAlg hOk hJ (c • t) f = c • heckeAlg hOk hJ t f
    rw [map_smul, LinearMap.smul_apply]
  · change heckeAlg hOk hJ (C c) f = c • f
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]
  · change ((heckeAlg hOk hJ (X i) f : Forms F.O (A := alg F.O N lam) F.Γ jK W) : F.G → W) g = _
    rw [heckeAlg_X]
    rfl

end GlobalTheory.ExpFrame.HeckeMod
