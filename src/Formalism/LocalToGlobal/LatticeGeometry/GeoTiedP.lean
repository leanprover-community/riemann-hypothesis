module

public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.NonemptyCoefficientFieldPrime
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
public import Formalism.LocalRingCardinality.SpanPowerMembership.PlOver
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Formalism.LocalToGlobal.LatticeGeometry.ShimuraSheafOfIndefiniteSubspace
public import Aesop.BuiltinRules
public import Formalism.LocalToGlobal.LatticeGeometry.InstAddCommSemigroupWt
public import Formalism.LocalToGlobal.LatticeGeometry.LevPrPrime
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.Divisibility.LocalNonemptiness.NonemptyBoundaryLocalIff, Formalism.LocalToGlobal.LatticeGeometry.InhabLoc, Formalism.LocalRingCardinality.SpanPowerMembership.PlLBridge, Formalism.LocalToGlobal.LatticeGeometry.Inhabited, Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP

-- ===== clump member: Formalism.SharpRestriction.Divisibility.LocalNonemptiness.NonemptyBoundaryLocalIff =====
-- clump-header: {"m": "Formalism.SharpRestriction.Divisibility.LocalNonemptiness.NonemptyBoundaryLocalIff", "h": "module\n\npublic import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions NumberField Formalism.MainNotions

def integersConjugation (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

theorem integers_conjugation_coe (D : D7) (c : 𝓞 D.host.E) : ((integersConjugation D c : 𝓞 D.host.E) : D.host.E) = D.host.conj (c : D.host.E) := rfl

def XT (_D : D7) (Y : Type) : Type := Y

instance (D : D7) (Y : Type) [AddCommGroup Y] : AddCommGroup (XT D Y) := inferInstanceAs (AddCommGroup Y)

instance (D : D7) (Y : Type) [AddCommGroup Y] [Module (𝓞 D.host.E) Y] : Module (𝓞 D.host.E) (XT D Y) :=
  Module.compHom Y (integersConjugation D)

def XT.mk (D : D7) (Y : Type) [AddCommGroup Y] : Y ≃+ XT D Y := AddEquiv.refl Y

theorem XT.smul_mk (D : D7) {Y : Type} [AddCommGroup Y] [Module (𝓞 D.host.E) Y] (c : 𝓞 D.host.E) (a : Y) :
    c • XT.mk D Y a = XT.mk D Y (integersConjugation D c • a) := rfl

theorem XT.symm_smul (D : D7) {Y : Type} [AddCommGroup Y] [Module (𝓞 D.host.E) Y] (c : 𝓞 D.host.E) (χ : XT D Y) :
    (XT.mk D Y).symm (c • χ) = integersConjugation D c • (XT.mk D Y).symm χ := rfl

theorem exists_alp (D : D7) (p n : ℕ) (h : ModuliIntegralCharts.NHyp D p n) : ∃ α : 𝓞 D.host.E,
    (α : D.host.E) * D.host.conj (α : D.host.E) = (n : D.host.E) ∧
    ((∃ mm : ℕ, n = mm ^ 2 ∧ α = (mm : 𝓞 D.host.E)) ∨ (α : D.host.E) ∈ D.host.K) := by
  obtain ⟨-, -, h⟩ := h
  rcases h with ⟨mm, rfl⟩ | ⟨π, hK, hπ⟩
  · refine ⟨(mm : 𝓞 D.host.E), ?_, Or.inl ⟨mm, rfl, rfl⟩⟩
    have h1 : ((mm : 𝓞 D.host.E) : D.host.E) = (mm : D.host.E) := by
      first
      | simp
    rw [h1, map_natCast]
    push_cast
    ring
  · exact ⟨π, hπ, Or.inr hK⟩

end Formalism.MainNotions.DIV.Inh

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.Divisibility.LocalNonemptiness.NonemptyBoundaryLocalIff =====

-- ===== clump member: Formalism.LocalToGlobal.LatticeGeometry.InhabLoc =====
-- clump-header: {"m": "Formalism.LocalToGlobal.LatticeGeometry.InhabLoc", "h": "module\n\npublic import Formalism.SharpRestriction.Divisibility.BoundaryLocalData\npublic import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.NonemptyCoefficientFieldPrime\npublic import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff\npublic import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.NonemptyBoundaryLocalIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Presheaf\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.L2.Geo

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts NumberField Formalism.MainNotions.DIV.Inh Formalism.MainNotions.DIV.Inh.LocalProvisionModel

def cfJunk (p : ℕ) : CF p := (nonempty_coefficient_field p).some

section Tools

def ballC (C : Type) [NormedField C] [IsUltrametricDist C] : AddSubgroup C where
  carrier := {x | ‖x‖ ≤ 1}
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem mem_ballC {C : Type} [NormedField C] [IsUltrametricDist C] (x : C) : x ∈ ballC C ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem intCast_mem_ballC {C : Type} [NormedField C] [IsUltrametricDist C] (t : ℤ) : (t : C) ∈ ballC C := by
  have h1 : (1 : C) ∈ ballC C := by
    rw [mem_ballC]
    simp
  simpa using (ballC C).zsmul_mem h1 t

theorem smul_mem_ballC {C : Type} [NormedField C] [IsUltrametricDist C] (a v : C) (ha : ‖a‖ ≤ 1) (hv : v ∈ ballC C) :
    a • v ∈ ballC C := by
  rw [mem_ballC, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hv

theorem span_intCast (C : Type) [Field C] : Submodule.span C (Set.range (Int.castAddHom C)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : (1 : C) ∈ Submodule.span C (Set.range (Int.castAddHom C)) := Submodule.subset_span ⟨1, by simp⟩
  simpa using Submodule.smul_mem _ x h1

theorem ballC_eq_inf {C : Type} [NormedField C] [IsUltrametricDist C] (a : C) :
    ballC C = ballC C ⊓ (Ospan (C := C) (Set.range (Int.castAddHom C)) ⊔
      (ballC C).map (DistribSMul.toAddMonoidHom C a)) := by
  refine le_antisymm (le_inf le_rfl (le_sup_of_le_left fun x hx => ?_)) inf_le_left
  exact AddSubgroup.subset_closure ⟨x, hx, 1, ⟨1, by simp⟩, by simp⟩

def actT (C A : Type) [Field C] [Group A] : Cˣ × A →* Module.End C C :=
  (algebraMap C (Module.End C C)).toMonoidHom.comp ((Units.coeHom C).comp (MonoidHom.fst Cˣ A))

def rkB (ρ : ℕ) : Bool → ℕ
  | false => 0
  | true => min ρ 1

theorem rkB_le_one (ρ : ℕ) (y : Bool) : rkB ρ y ≤ 1 := by
  cases y <;> simp [rkB]

theorem rkB_le (ρ : ℕ) (y : Bool) : rkB ρ y ≤ ρ := by
  cases y <;> simp [rkB]

theorem le_choose_two (r : ℕ) : r - 1 ≤ r * (r - 1) / 2 := by
  rcases r with _ | _ | k
  · simp
  · simp
  · rw [Nat.le_div_iff_mul_le (by norm_num)]
    simp only [Nat.add_sub_cancel]
    nlinarith

theorem flDim_eq (f r : ℕ) : f * (r * (r - 1) / 2) - f * (r - 1) + f * (r - 1) = f * (r * (r - 1) / 2) :=
  Nat.sub_add_cancel (Nat.mul_le_mul_left _ (le_choose_two r))


open Matrix in
theorem pd_of_int {Y : Type} [AddCommGroup Y] (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)
    (hsymm : ∀ a b, β a b = β b a) (hint : ∀ a b, ∃ z : ℤ, β a b = z) (hpos : ∀ a, a ≠ 0 → 0 < β a a)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ Y) (x : Fin n → ℝ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ k, x i * x k * β (b i) (b k) := by
  classical
  choose g hg using fun i k => hint (b i) (b k)
  let G : Matrix (Fin n) (Fin n) ℤ := Matrix.of g
  let GR : Matrix (Fin n) (Fin n) ℝ := G.map (Int.castRingHom ℝ)
  have hGR : ∀ i k, GR i k = β (b i) (b k) := fun i k => by simp [GR, G, hg]
  have hq : ∀ x : Fin n → ℝ, ∑ i, ∑ k, x i * x k * β (b i) (b k) = x ⬝ᵥ (GR *ᵥ x) := by
    intro x
    simp only [dotProduct, Matrix.mulVec, hGR, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hz : ∀ z : Fin n → ℤ, (fun i => (z i : ℝ)) ⬝ᵥ (GR *ᵥ fun i => (z i : ℝ)) =
      β (∑ i, z i • b i) (∑ i, z i • b i) := by
    intro z
    rw [← hq]

    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by
      rw [hsymm (b k) (b i)]
      ring
  have hhom : ∀ (t : ℝ) (x : Fin n → ℝ), (t • x) ⬝ᵥ (GR *ᵥ (t • x)) = t ^ 2 * (x ⬝ᵥ (GR *ᵥ x)) := by
    intro t x
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hnnZ : ∀ z : Fin n → ℤ, 0 ≤ (fun i => (z i : ℝ)) ⬝ᵥ (GR *ᵥ fun i => (z i : ℝ)) := by
    intro z
    rw [hz]
    by_cases h : (∑ i, z i • b i) = 0
    · rw [h]
      simp
    · exact (hpos _ h).le
  have hnnQ : ∀ w : Fin n → ℚ, 0 ≤ (fun i => (w i : ℝ)) ⬝ᵥ (GR *ᵥ fun i => (w i : ℝ)) := by
    intro w
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) Finset.univ w
    choose z hz' using fun i => hd i (Finset.mem_univ i)
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    have h1 : (fun i => (z i : ℝ)) = ((d : ℤ) : ℝ) • fun i => (w i : ℝ) := by
      funext i
      have h2 := congrArg (fun q : ℚ => (q : ℝ)) (hz' i)
      simpa using h2
    have h2 := hnnZ z
    rw [h1, hhom] at h2
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 h2
  have hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (GR *ᵥ x) := by
    intro x
    have hdense : DenseRange (Pi.map fun (_ : Fin n) (q : ℚ) => (q : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hdense.induction_on x ?_ hnnQ
    refine isClosed_le continuous_const ?_
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨z, hz0, hGz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 := hz z
    have h2 : GR *ᵥ (fun i => (z i : ℝ)) = 0 := by
      funext i
      show (G.map (Int.castRingHom ℝ) *ᵥ ((Int.castRingHom ℝ) ∘ z)) i = 0
      rw [← RingHom.map_mulVec, hGz]
      simp
    rw [h2, dotProduct_zero] at h1
    have h3 : ∑ i, z i • b i ≠ 0 := fun h =>
      hz0 (funext fun i => Fintype.linearIndependent_iff.1 b.linearIndependent z h i)
    exact (hpos _ h3).ne h1
  have hherm : GR.IsHermitian := by
    ext i k
    simp [Matrix.conjTranspose_apply, hGR, hsymm (b k) (b i)]
  have hPS : GR.PosSemidef := .of_dotProduct_mulVec_nonneg hherm fun x => by simpa using hpsd x
  have hU : IsUnit GR := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    have h1 : GR.det = ((G.det : ℤ) : ℝ) := ((Int.castRingHom ℝ).map_det G).symm
    rw [h1]
    exact_mod_cast hdet
  have hPD := hPS.posDef_iff_isUnit.2 hU
  rw [hq]
  simpa using hPD.dotProduct_mulVec_pos hx

variable (D : D7)

theorem subsingleton_pow (k : ℕ) : Subsingleton (Fin k → 𝓞 D.host.E) ↔ k = 0 := by
  constructor
  · intro hs
    by_contra hk
    have := hs.elim (fun _ => (0 : 𝓞 D.host.E)) (fun _ => 1)
    exact zero_ne_one (congrFun this ⟨0, Nat.pos_of_ne_zero hk⟩)
  · rintro rfl
    infer_instance

theorem finrank_OE : Module.finrank ℤ (𝓞 D.host.E) = 2 * D.R.f := by
  rw [RingOfIntegers.rank, D.host.finrank_cmField]
  simp only [Ranks.f, Ranks.n]
  ring

theorem finrank_pow (k : ℕ) : Module.finrank ℤ (Fin k → 𝓞 D.host.E) = k * (2 * D.R.f) := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, finrank_OE]
  simp

def trZ (k : ℕ) (a b : Fin k → 𝓞 D.host.E) : ℤ := ∑ i, Algebra.trace ℤ (𝓞 D.host.E) (a i * cjO D (b i))

theorem trZ_cast (k : ℕ) (a b : Fin k → 𝓞 D.host.E) : ((trZ D k a b : ℤ) : ℝ) = beK D k a b := by
  rw [beK_apply, trZ, Int.cast_sum]
  rfl

theorem beK_symm (k : ℕ) (a b : Fin k → 𝓞 D.host.E) : beK D k a b = beK D k b a := by
  rw [beK_apply, beK_apply]
  exact Finset.sum_congr rfl fun i _ => beO_symm D _ _

theorem beK_bal (k : ℕ) (c c' : 𝓞 D.host.E) (h : (c' : D.host.E) = D.host.conj (c : D.host.E))
    (a b : Fin k → 𝓞 D.host.E) : beK D k (c • a) b = beK D k a (c' • b) := by
  rw [beK_apply, beK_apply]
  exact Finset.sum_congr rfl fun i _ => beO_bal D c c' h _ _

theorem trZ_add_left (k : ℕ) (a a' b : Fin k → 𝓞 D.host.E) : trZ D k (a + a') b = trZ D k a b + trZ D k a' b := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_add, trZ_cast, trZ_cast, trZ_cast, map_add (f := _), LinearMap.add_apply]

theorem trZ_add_right (k : ℕ) (a b b' : Fin k → 𝓞 D.host.E) : trZ D k a (b + b') = trZ D k a b + trZ D k a b' := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_add, trZ_cast, trZ_cast, trZ_cast, map_add (f := _)]

theorem trZ_symm (k : ℕ) (a b : Fin k → 𝓞 D.host.E) : trZ D k a b = trZ D k b a := by
  apply Int.cast_injective (α := ℝ)
  rw [trZ_cast, trZ_cast, beK_symm]

theorem trZ_bal (k : ℕ) (c : 𝓞 D.host.E) (a b : Fin k → 𝓞 D.host.E) :
    trZ D k (c • a) b = trZ D k a (integersConjugation D c • b) := by
  apply Int.cast_injective (α := ℝ)
  rw [trZ_cast, trZ_cast, beK_bal D k c (integersConjugation D c) (integers_conjugation_coe D c)]

theorem trZ_self_nonneg (k : ℕ) (a : Fin k → 𝓞 D.host.E) : 0 ≤ trZ D k a a := by
  have h : (0 : ℝ) ≤ ((trZ D k a a : ℤ) : ℝ) := by
    rw [trZ_cast, beK_apply]
    exact Finset.sum_nonneg fun i _ => beO_nonneg D _
  exact_mod_cast h

theorem trZ_zero_rank (a b : Fin 0 → 𝓞 D.host.E) : trZ D 0 a b = 0 := by
  simp [trZ]


open Classical in
def pU (p : ℕ) (c : CF p) : (c.C)ˣ := if h : (p : c.C) = 0 then 1 else Units.mk0 (p : c.C) h

theorem vU_pU_zpow (p : ℕ) (c : CF p) (z : ℤ) (h : 2 ≤ p ∨ z = 0) : BoundaryLocalData.vU p (pU p c ^ z) = z := by
  rcases h with h | rfl
  · have hp0 : (p : c.C) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h1 : ((pU p c ^ z : (c.C)ˣ) : c.C) = (p : c.C) ^ z := by simp [pU, hp0]
    have hl : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast h)).ne'
    unfold BoundaryLocalData.vU Real.logb
    rw [h1, norm_zpow, c.norm_p, Real.log_zpow, Real.log_inv]
    field_simp
  · simp [BoundaryLocalData.vU]

def u2 : (FractionRing ℤ_[2])ˣ :=
  Units.mk0 (algebraMap ℤ_[2] (FractionRing ℤ_[2]) 2)
    ((map_ne_zero_iff _ (IsFractionRing.injective ℤ_[2] (FractionRing ℤ_[2]))).2 two_ne_zero)

theorem two_adic_unit_zpow_mem (z : ℤ) (hz : 0 ≤ z) :
    ((u2 ^ z : (FractionRing ℤ_[2])ˣ) : FractionRing ℤ_[2]) ∈ (algebraMap ℤ_[2] (FractionRing ℤ_[2])).range := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  exact ⟨2 ^ n, by simp [u2]⟩

end Tools

section Model

variable (D : D7) (r j p : ℕ) (c : CF p) (ρ : ℕ)

@[reducible] def locT : Loc D r j p where
  Mdl := Unit
  Xm := ()
  YY := ()
  Xn := fun _ => ()
  Pt := fun _ => Bool
  fld := fun _ => c
  Ylat := fun y => Fin (rkB ρ y) → 𝓞 D.host.E
  ylAdd := fun _ => inferInstance
  ylMod := fun _ => inferInstance
  ylFree := fun _ => inferInstance
  ylFin := fun _ => inferInstance
  be := fun y => beK D (rkB ρ y)
  be_symm := fun y a b => beK_symm D _ a b
  be_bal := fun y e e' h a b => beK_bal D _ e e' h a b
  be_posDef := fun y => ⟨Fin _, inferInstance, Module.finBasis ℤ _, fun x hx => pd_of_int (beK D (rkB ρ y))
    (fun a b => beK_symm D _ a b) (fun a a' => beK_int D (rkB ρ y) a a') (fun a h => beK_pos D _ a h) _ x hx⟩
  yl_rank := fun y => ⟨rkB ρ y, by rw [finrank_pow]; ring, fun h1 h2 => by
    have := rkB_le_one ρ y; omega⟩
  Gen := fun _ => Bool
  abAt := fun η => rkB ρ η = 0
  Sh := fun _ => Unit
  IsInv := fun _ => True
  IsLocFree := fun _ => True
  Sec := fun _ => c.C
  secAdd := fun _ => inferInstance
  H0 := fun _ => ballC c.C
  nrm := fun _ f _ => ‖f‖
  nrm_nonneg := fun _ f _ => norm_nonneg f
  norm_le_one_of_mem_sections := fun _ _ h _ => h
  GIso := fun _ _ => Unit
  vrat := fun _ _ => 0
  Lb := fun _ => ()
  Lb_inv := fun _ => trivial
  nrmRef := fun _ f _ => ‖f‖
  DVP := Bool
  dvRho := fun y => rkB ρ y
  Ext := fun _ => Unit
  Chart := fun _ _ _ => Unit
  chAt := fun _ => True
  chOpen := fun _ => True
  chAbExact := fun {_ y _} _ => 0 < rkB ρ y
  chModU := fun _ => True
  chConst := fun _ => True
  PL := Unit
  phiAt := fun _ _ _ => 0
  phiAt_zero := fun _ _ _ _ => rfl
  divGe := fun _ _ _ _ => True
  FJd := Unit
  Chr := fun _ => Unit
  fjN := fun _ f _ _ => ‖f‖
  Unim := ℕ
  LBG := fun _ => Unit
  LBGq := fun _ => Unit
  resQ := fun _ => ()
  PPq := fun _ => ()
  symmG := fun _ => True
  rigG := fun _ => True
  LBGt := fun _ _ => Unit
  LBB := fun _ _ => Unit
  resGt := fun _ _ => ()
  prPull := fun _ => ()
  principal := fun _ => True
  psiV := fun y a => beK D (rkB ρ y) a (BoundaryLocalData.w0 D • a)
  piPP := ()
  keySh := fun _ => ()
  latStd := fun n => n
  At := fun _ La n => AtM (2 * (D.R.f * r * La)) n
  atAdd := fun _ _ _ => inferInstance
  atFin := fun _ _ _ => inferInstance
  at_tors := fun _ _ _ x => atM_tors _ _ x
  at_card := fun _ _ _ h => atM_card _ _ h
  Th := fun _ La n => (c.C)ˣ × Multiplicative (AtM (2 * (D.R.f * r * La)) n)
  thGrp := fun _ _ _ => inferInstance
  ovr := fun _ _ _ => MonoidHom.snd _ _
  ovr_surj := fun _ _ _ x => ⟨(1, x), rfl⟩
  scal := fun _ _ _ => MonoidHom.inl _ _
  scal_inj := fun _ _ _ a b h => congrArg Prod.fst h
  scal_central := fun _ _ _ a g => by
    ext <;> simp [mul_comm]
  ker_ovr := fun _ _ _ g => ⟨fun h => ⟨g.1, Prod.ext rfl h.symm⟩, fun ⟨a, h⟩ => by rw [← h]; rfl⟩
  dl := fun _ _ _ => MulEquiv.prodCongr (MulEquiv.refl _) (MulEquiv.inv _)
  dl_ovr := fun _ _ _ _ => rfl
  dl_scal := fun _ La n a => Prod.ext rfl (inv_one : (1 : Multiplicative (AtM (2 * (D.R.f * r * La)) n))⁻¹ = 1)
  dl_dl := fun _ _ _ g => by
    show (g.1, (g.2⁻¹)⁻¹) = g
    rw [inv_inv]
  Sn := fun _ _ _ => c.C
  snAdd := fun _ _ _ => inferInstance
  snMod := fun _ _ _ => inferInstance
  act := fun _ La n => actT c.C (Multiplicative (AtM (2 * (D.R.f * r * La)) n))
  act_scal := fun _ _ _ _ _ => rfl
  vth := fun _ _ _ => 1
  Jet := fun _ _ _ _ => c.C
  jAdd := fun _ _ _ _ => inferInstance
  jMod := fun _ _ _ _ => inferInstance
  intJet := fun _ _ _ _ => ballC c.C
  jet := fun _ _ _ _ => LinearMap.id
  LieGt := fun _ _ => PUnit
  LieB := fun _ _ => PUnit
  LieT := fun _ _ => PUnit
  lgAdd := fun _ _ => inferInstance
  lbAdd := fun _ _ => inferInstance
  ltAdd := fun _ _ => inferInstance
  resB := fun _ _ => 0
  incT := fun _ _ => 0
  kapGt := fun _ _ _ _ => 0
  kapB := fun _ _ _ _ => 0
  Harm := fun _ => Unit
  SecP := fun _ => Unit
  evA := fun _ _ _ => 0
  evGt := fun _ _ _ => 0
  Tp := fun _ => ℤ
  tpAdd := fun _ => inferInstance
  OmV := fun _ => c.C
  omAdd := fun _ => inferInstance
  omMod := fun _ => inferInstance
  om := fun _ => ballC c.C
  ht := fun _ => Int.castAddHom c.C
  IsHTBlowup := fun _ _ => True
  eOmP := fun _ _ _ => ()
  SES := fun _ => Unit
  ExactMod := fun _ _ => True
  htSES := fun _ _ => ()
  nefHT := fun _ _ => True
  nefQ := fun _ => True
  descK := fun _ _ => True
  bdryLoci := fun _ => True
  BT := fun _ => Unit
  extA := fun _ => True
  compat := fun _ _ => True
  Crv := PsiT D → ℕ → ℤ
  eDeg := fun d => -∑ᶠ τ, ((∑ i ∈ Finset.Icc 1 j, d τ i) + -∑ i ∈ Finset.Icc (j + 1) r, d τ i)
  Pm := fun d => pmM D d (r + j)
  Pm_nonneg := fun d => pmM_nonneg D _ _
  degLie := fun d τ b => if b then -∑ i ∈ Finset.Icc (j + 1) r, d τ i else ∑ i ∈ Finset.Icc 1 j, d τ i
  degLdR := fun d μ => -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 r, μ τ i * (d τ i : ℝ)

@[reducible] def extT : ExtA D (locT D r j p c ρ) where
  FlagData := fun _ => Unit
  flagCl := fun _ _ => ()
  allFlags := ()
  YY_eq := rfl
  Idl := fun _ => Unit
  blowUp := fun _ _ => ()
  powP := fun _ => True
  pbPrinc := fun _ _ => True
  Corr := fun _ _ => Unit
  diagCl := fun _ _ _ => ()
  IvD := fun _ => Unit
  jIdl := fun _ _ => ()
  ZP := fun _ => Bool × Bool
  spz := fun x x' => (x'.1 = true → x.1 = true) ∧ (x'.2 = true → x.2 = true)
  abP := fun x => x.2 = true
  inQ := fun x => x.1 = true
  isGenP := fun x => x = (true, true)
  isGenP_ab := fun x h => by rw [h]
  gpt := fun η => (false, decide (rkB ρ η = 0))
  abAt_iff := fun η => by
    show rkB ρ η = 0 ↔ decide (rkB ρ η = 0) = true
    rw [decide_eq_true_eq]
  gpt_notQ := fun _ h => Bool.false_ne_true h
  genFin := fun _ => inferInstanceAs (Finite Bool)
  genNe := fun _ => ⟨false⟩
  redK := fun _ y => (false, decide (rkB ρ y = 0))
  dvRho_pos_iff := fun _ y => by
    show 0 < rkB ρ y ↔ ¬ decide (rkB ρ y = 0) = true
    rw [decide_eq_true_eq]
    omega
  genK := fun η => η
  redK_genK := fun _ => rfl
  imgM := fun {_ y _} _ => (false, decide (rkB ρ y = 0))
  imgU := fun {_ y _} _ => (true, decide (rkB ρ y = 0))
  img_spz := fun _ => ⟨fun h => absurd h Bool.false_ne_true, fun h => h⟩
  imgU_inQ := fun _ => rfl
  chAt_imgM := fun _ _ => rfl
  chAbExact_imgU := fun {_ y _} _ h => by
    show ¬ decide (rkB ρ y = 0) = true
    rw [decide_eq_true_eq]
    exact Nat.pos_iff_ne_zero.1 h
  RFam := fun _ _ => Unit
  chFam := fun _ => ()
  ptK := fun _ y => y
  ptK_good := fun _ y => subsingleton_pow D (rkB ρ y)
  vpi := fun _ => 1
  vpi_pos := fun _ => one_pos
  ordGe := fun _ _ _ _ => True
  yEta := fun η => η
  yEta_good := fun η => subsingleton_pow D (rkB ρ η)
  homSh := fun _ _ => ()
  homSh_inv := fun _ _ _ _ => trivial
  isoSec := fun _ => (1 : c.C)
  nrm_isoSec := fun _ _ => by
    show ‖(1 : c.C)‖ = (p : ℝ) ^ (-(0 : ℝ))
    simp
  isoSymm := fun _ => ()
  vrat_symm := fun _ _ => by
    show (0 : ℝ) = -0
    simp
  LieV := fun _ => c.C
  lvAdd := fun _ => inferInstance
  lvMod := fun _ => inferInstance
  lieL := fun _ => ballC c.C
  eig := fun _ _ => ⊤
  Wst := fun _ _ _ => ⊤
  Wst_le := fun _ _ _ => le_rfl
  taut := fun _ _ _ => ballC c.C
  taut_eq := fun _ _ _ => by simp
  nrmIn := fun _ f _ _ => ‖f‖
  nrmRef_def := fun _ _ _ => rfl
  nrm_Lb_def := fun _ _ _ => rfl
  om_smul := fun _ a ha v hv => smul_mem_ballC a v ha hv
  TC := fun _ => c.C
  tcAdd := fun _ => inferInstance
  tcMod := fun _ => inferInstance
  iT := fun _ => Int.castAddHom c.C
  iT_span := fun _ => span_intCast c.C
  htC := fun _ => LinearMap.id
  htC_iT := fun _ _ => rfl
  psiC := fun _ => 0
  lieGt1 := fun _ => ⊥
  eT := fun _ _ => LinearMap.id
  HTn := fun _ => Unit
  htEval := fun _ _ => Int.castAddHom c.C
  htIdl := fun _ => ()
  IsHTBlowup_def := fun _ _ _ =>
    ⟨fun _ => ⟨(), fun _ t => ⟨intCast_mem_ballC t, 0, zero_mem _, by simp⟩, rfl⟩, fun _ => trivial⟩
  wFib := fun _ _ _ => ballC c.C
  htFlags := fun _ => ()
  omSh := fun _ => ()
  omPat := fun _ => ballC c.C
  omPat_def := fun _ _ _ _ _ => ballC_eq_inf _
  BPt := fun _ => Unit
  bfld := fun _ => c
  OmB := fun _ => c.C
  obAdd := fun _ => inferInstance
  obMod := fun _ => inferInstance
  omB := fun _ => ballC c.C
  omPB := fun _ => ballC c.C
  eOmB := fun _ _ => ballC c.C
  eB := fun _ _ => LinearMap.id
  YsP := fun _ => Bool
  ysBd := fun x => x = true
  FlP := Unit
  hFl := fun _ => ()
  FlCl := Unit
  flMem := fun _ _ => True
  flDim := fun _ => D.R.f * (r * (r - 1) / 2) - D.R.f * (r - 1)
  Sum1 := Unit
  locus := fun _ => ()
  bdryLoci_def := fun _ =>
    ⟨fun _ => ⟨Set.univ, Set.finite_univ, fun _ _ => ⟨(), trivial, trivial⟩, fun _ _ => flDim_eq D.R.f r⟩,
      fun _ => trivial⟩
  CrvS := fun _ => Unit
  degGr := fun _ _ _ => 0
  nefHT_def := fun _ _ => ⟨fun _ _ => by simp, fun _ => trivial⟩
  CrvQ := Unit
  degGrQ := fun _ _ _ => 0
  nefQ_def := fun _ => ⟨fun _ _ => by simp, fun _ => trivial⟩
  degGrD := fun d => d
  degLdR_def := fun _ _ => rfl
  degLie_f := fun _ _ => rfl
  degLie_alt := fun _ _ => rfl
  eDeg_def := fun _ _ => rfl
  Pm_head := fun d τ i _ h2 => le_trans (le_abs_self _)
    (abs_le_pmM D d (r + j) τ _ (Finset.Icc_subset_Icc le_rfl (by omega)))
  Pm_tail := fun d τ i _ _ => le_trans (neg_le_abs _)
    (abs_le_pmM D d (r + j) τ _ (Finset.Icc_subset_Icc (by omega) (by omega)))


open Classical in
@[reducible] def locBT (hp : 2 ≤ p ∨ ρ = 0) (hd : ρ * (2 * D.R.f) ≤ D.R.f * r) :
    BoundaryLocalData.LocB D (locT D r j p c ρ) where
  chX := fun {_} y => XT D (Fin (rkB ρ y) → 𝓞 D.host.E)
  xAdd := fun {_} _ => inferInstance
  xMod := fun {_} _ => inferInstance
  phi := fun {_} y => XT.mk D (Fin (rkB ρ y) → 𝓞 D.host.E)
  phi_conj := fun {_} y e e' h a => by
    have : e' = integersConjugation D e := RingOfIntegers.ext (by rw [h, integers_conjugation_coe])
    rw [this, XT.smul_mk]
  tau := fun {_} y a χ => pU p c ^ trZ D (rkB ρ y) a ((XT.mk D (Fin (rkB ρ y) → 𝓞 D.host.E)).symm χ)
  tau_add_left := fun {_} y a a' χ => by rw [trZ_add_left, zpow_add]
  tau_add_right := fun {_} y a χ χ' => by rw [map_add (f := _), trZ_add_right, zpow_add]
  tau_symm := fun {_} y a b => congrArg (fun z : ℤ => pU p c ^ z) (trZ_symm D (rkB ρ y) a b)
  tau_smul := fun {_} y e a χ => by rw [XT.symm_smul, trZ_bal]
  be_tau := fun {_} y a b => by
    show beK D (rkB ρ y) a b = BoundaryLocalData.vU p (pU p c ^ trZ D (rkB ρ y) a b)
    rw [vU_pU_zpow, trZ_cast]
    rcases hp with hp | rfl
    · exact Or.inl hp
    · cases y <;> exact Or.inr (trZ_zero_rank D _ _)
  multiplicationLatticeFirst := fun {_} y _ b => XT.mk D (Fin (rkB ρ y) → 𝓞 D.host.E) b
  multiplicationLatticeSecond := fun {_} y a _ => XT.mk D (Fin (rkB ρ y) → 𝓞 D.host.E) a
  mulC := fun {_} y a b => pU p c ^ trZ D (rkB ρ y) a b
  psiV_def := fun {_} y a => by
    show beK D (rkB ρ y) a (BoundaryLocalData.w0 D • a) = BoundaryLocalData.vU p (pU p c ^ trZ D (rkB ρ y) a (BoundaryLocalData.w0 D • a))
    rw [vU_pU_zpow, trZ_cast]
    rcases hp with hp | rfl
    · exact Or.inl hp
    · cases y <;> exact Or.inr (trZ_zero_rank D _ _)
  StrictHenselianAcyclic := fun _ => Unit
  squareRootLineBundle := fun _ => Unit
  res2 := fun {_} _ => ()
  PoiQ := fun _ => ()
  biext := fun {_} _ => True
  dg := fun {_} _ => ()
  dgq := fun {_} _ => ()
  dg_res := fun {_} _ => rfl
  PPq_def := fun _ => rfl
  BPt := Unit
  Rl := fun _ => ℤ_[2]
  iRr := fun _ => inferInstance
  iRd := fun _ => inferInstance
  iRl := fun _ => inferInstance
  iRn := fun _ => inferInstance
  iRi := fun _ => inferInstance
  iRc := fun _ => inferInstance
  Yb := fun _ => Fin 1 → 𝓞 D.host.E
  iYa := fun _ => inferInstance
  iYm := fun _ => inferInstance
  Xb := fun _ => XT D (Fin 1 → 𝓞 D.host.E)
  iXa := fun _ => inferInstance
  iXm := fun _ => inferInstance
  phib := fun _ => XT.mk D (Fin 1 → 𝓞 D.host.E)
  phib_conj := fun _ e e' h a => by
    have : e' = integersConjugation D e := RingOfIntegers.ext (by rw [h, integers_conjugation_coe])
    rw [this, XT.smul_mk]
  taub := fun _ a χ => u2 ^ trZ D 1 a ((XT.mk D (Fin 1 → 𝓞 D.host.E)).symm χ)
  taub_add_left := fun _ a a' χ => by rw [trZ_add_left, zpow_add]
  taub_add_right := fun _ a χ χ' => by rw [map_add (f := _), trZ_add_right, zpow_add]
  taub_symm := fun _ a b => congrArg (fun z : ℤ => u2 ^ z) (trZ_symm D 1 a b)
  taub_smul := fun _ e a χ => by rw [XT.symm_smul, trZ_bal]
  taub_pos := fun _ a => two_adic_unit_zpow_mem _ (trZ_self_nonneg D 1 a)
  Sg := fun _ => FractionRing ℤ_[2]
  iSg := fun _ => inferInstance
  iSk := fun _ => inferInstance
  iSm := fun _ => inferInstance
  iSt := fun _ => inferInstance
  Sreg := fun _ => LinearMap.range (Algebra.linearMap ℤ_[2] (FractionRing ℤ_[2]))
  fc := fun _ => LinearMap.pi fun _ => LinearMap.id
  trU := fun _ _ _ => 1
  oX := ()
  oX_inv := trivial
  secOf := fun {_} _ => (1 : c.C)
  nrm_secOf := fun {_} _ _ => by
    show ‖(1 : c.C)‖ = (p : ℝ) ^ (-(0 : ℝ))
    simp
  keySh_inv := fun _ _ => trivial
  dimB := fun y => D.R.f * r - rkB ρ y * (2 * D.R.f)
  dimB_add := fun y => by
    show D.R.f * r - rkB ρ y * (2 * D.R.f) + Module.finrank ℤ (Fin (rkB ρ y) → 𝓞 D.host.E) = D.R.f * r
    rw [finrank_pow]
    refine Nat.sub_add_cancel ?_
    cases y
    · simp [rkB]
    · exact (Nat.mul_le_mul_right _ (rkB_le ρ true)).trans hd
  FB := fun _ _ _ _ => c.C
  fbAdd := fun _ _ _ _ => inferInstance
  fbMod := fun _ _ _ _ => inferInstance
  nB := fun {_ _ _ _} σ => ‖σ‖
  sgc := fun _ _ _ χ => if χ = 0 then LinearMap.id else 0
  trB := fun _ _ _ _ _ => LinearEquiv.refl c.C c.C
  trB_norm := fun _ _ _ _ _ _ => rfl
  alp := fun n => if h : ModuliIntegralCharts.NHyp D p n then (exists_alp D p n h).choose else 0
  alp_spec := fun n h => by
    rw [dite_eq_left h]
    exact (exists_alp D p n h).choose_spec
  th1 := fun _ _ => (1 : c.C)
  pbAl := fun _ _ _ => LinearMap.id
  vth_def := fun _ _ _ _ => rfl
  jX := fun _ _ _ _ _ => LinearMap.id
  intJet_free := fun _ _ _ _ =>
    ⟨1, Module.Basis.singleton (Fin 1) c.C, fun v =>
      ⟨fun h i => by simpa using (mem_ballC v).1 h, fun h => (mem_ballC v).2 (by simpa using h 0)⟩⟩
  jX_int := fun _ _ _ _ _ _ h => h
  jet_fourier := fun y nW n DF s t _ => by
    refine ⟨{0}, fun F hF => ⟨0, zero_mem _, ?_⟩⟩
    have h0 : (0 : Fin nW → XT D (Fin (rkB ρ y) → 𝓞 D.host.E)) ∈ F := hF (Finset.mem_singleton_self 0)
    rw [Finset.sum_eq_single_of_mem 0 h0 (fun χ _ hχ => by simp [hχ])]
    simp

end Model

def rhoJ (r p : ℕ) : ℕ := if 2 ≤ r ∧ 2 ≤ p then 1 else 0

theorem rhoJ_p (r p : ℕ) : 2 ≤ p ∨ rhoJ r p = 0 := by
  unfold rhoJ
  split_ifs with h
  · exact Or.inl h.2
  · exact Or.inr rfl

theorem rhoJ_dim (f r p : ℕ) : rhoJ r p * (2 * f) ≤ f * r := by
  unfold rhoJ
  split_ifs with h
  · nlinarith [h.1]
  · simp

def junkLocalData (D : D7) (r j p : ℕ) : ModuliIntegralCharts.Loc D r j p := locT D r j p (cfJunk p) (rhoJ r p)

def exJunk (D : D7) (r j p : ℕ) : ModuliIntegralCharts.ExtA D (junkLocalData D r j p) := extT D r j p (cfJunk p) (rhoJ r p)

def junkLocBAll (D : D7) (r j p : ℕ) : BoundaryLocalData.LocB D (junkLocalData D r j p) :=
  locBT D r j p (cfJunk p) (rhoJ r p) (rhoJ_p r p) (rhoJ_dim D.R.f r p)

def junkLocB (D : D7) (r j p : ℕ) (_hp : p.Prime) : BoundaryLocalData.LocB D (junkLocalData D r j p) := junkLocBAll D r j p

section Facts

variable (D : D7) (r j p : ℕ) (c : CF p) (ρ : ℕ)

variable {D r j p}

end Facts

end Formalism.L2.Geo

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.LatticeGeometry.InhabLoc =====

-- ===== clump member: Formalism.LocalRingCardinality.SpanPowerMembership.PlLBridge =====
-- clump-header: {"m": "Formalism.LocalRingCardinality.SpanPowerMembership.PlLBridge", "h": "module\n\npublic import Formalism.LocalRingCardinality.SpanPowerMembership.PlOver\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\npublic import Mathlib.NumberTheory.RamificationInertia.Inertia\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.PlOver

open NumberField IsDedekindDomain

variable (D : D7)

def plLEquiv (p : ℕ) [Fact p.Prime] :
    {v : HeightOneSpectrum (𝓞 D.what₂.LL) // ((p : ℕ) : 𝓞 D.what₂.LL) ∈ v.asIdeal} ≃
      {w : D.what₂.places.Pl // D.what₂.places.resChar w = p} :=
  (D.plEq.subtypeEquiv (fun w => resChar_eq_iff D p w)).symm

theorem plEq_plLEquiv (p : ℕ) [Fact p.Prime]
    (v : {v : HeightOneSpectrum (𝓞 D.what₂.LL) // ((p : ℕ) : 𝓞 D.what₂.LL) ∈ v.asIdeal}) :
    D.plEq (plLEquiv D p v).1 = v.1 := D.plEq.apply_symm_apply v.1

theorem wtLog_eq (p : ℕ) [hp : Fact p.Prime]
    (v : {v : HeightOneSpectrum (𝓞 D.what₂.LL) // ((p : ℕ) : 𝓞 D.what₂.LL) ∈ v.asIdeal}) :
    (eWL D.what₂.LL v.1 : ℝ) * Real.log (Ideal.absNorm v.1.asIdeal : ℝ) /
        (Real.log (p : ℝ) * (Module.finrank ℚ D.what₂.LL : ℝ)) =
      (D.what₂.places.ramIdx (plLEquiv D p v).1 : ℝ) *
        (padicValNat p (Ideal.absNorm (D.plEq (plLEquiv D p v).1).asIdeal) : ℝ) /
        (Module.finrank ℚ D.what₂.LL : ℝ) := by
  rw [D.ram_eq, plEq_plLEquiv]
  have := v.1.isPrime
  have : v.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_of_mem _ v.2
  rw [Ideal.absNorm_eq_pow_inertiaDeg' (p := p) _ hp.out, Nat.padicValNat_def, Nat.multiplicity_prime_pow]
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  have h0 : (Module.finrank ℚ D.what₂.LL : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  push_cast
  rw [Real.log_pow]
  field_simp

end Formalism.BasicNotions.Examples₂.PlOver
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalRingCardinality.SpanPowerMembership.PlLBridge =====

-- ===== clump member: Formalism.LocalToGlobal.LatticeGeometry.Inhabited =====
-- clump-header: {"m": "Formalism.LocalToGlobal.LatticeGeometry.Inhabited", "h": "module\n\npublic import Formalism.LocalToGlobal.LatticeGeometry.ShimuraSheafOfIndefiniteSubspace\npublic import Formalism.LocalToGlobal.LatticeGeometry.InhabLoc\npublic import Formalism.LocalRingCardinality.SpanPowerMembership.PlLBridge\npublic import Aesop.BuiltinRules\npublic import Formalism.LocalToGlobal.LatticeGeometry.InstAddCommSemigroupWt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.DIV.Inh Formalism.MainNotions.DIV.Inh.LocalProvisionModel

namespace Formalism.L2.Geo

def geoDegenerateNoTau (F : Type) [Field F] [NumberField F] [StarRing F] : DV.Geo F where
  Var := ℕ
  dim := id
  Fn := fun _ => F
  fnField := fun _ => inferInstanceAs (Field F)
  fnAlg := fun _ => inferInstanceAs (Algebra F F)
  Dv := fun _ => ℤ
  dvGrp := fun _ => inferInstanceAs (AddCommGroup ℤ)
  Eff := fun _ _ => True
  eff_zero := fun _ => trivial
  eff_add := fun _ _ _ _ _ => trivial
  H0 := fun _ _ => ⊥
  degreeZeroCohomology_finiteDimensional := fun _ _ => inferInstance
  mul_mem_riemannRochSpace_add := fun _ _ _ f g hf _ => by
    rw [Submodule.mem_bot] at hf ⊢; simp [hf]
  riemannRoch_mono := fun _ _ _ _ => le_refl _
  KY := fun _ => (0 : ℤ)
  Cl := fun _ => PUnit
  properCl := fun _ _ => True
  subCl := fun _ _ _ => True
  supp := fun _ _ => PUnit.unit
  inter := fun _ _ => 0
  nef := fun _ _ => True
  big := fun _ _ => True
  bpf := fun _ _ _ => True
  phiBir := fun _ _ _ => True
  phiNoContr := fun _ _ _ _ => True
  vanishOn := fun _ _ _ _ => True
  hdim := fun _ _ _ => 0
  pts := fun _ _ => PUnit
  ptsMeas := fun _ _ => ⊤
  vol := fun _ _ => 0
  FnC := fun _ _ => ℂ
  fnCRing := fun _ _ => inferInstanceAs (CommRing ℂ)
  fnCAlg := fun _ _ => inferInstanceAs (Algebra ℂ ℂ)
  cx := fun _ σ => σ
  cx_smul := fun _ σ a f => by
    show σ (a * f) = σ a * σ f
    exact map_mul σ a f
  Met := fun _ _ _ => PUnit
  mAdd := fun _ _ _ _ _ _ => PUnit.unit
  mPow := fun _ _ _ _ _ => PUnit.unit
  fsMet := by intros; exact PUnit.unit
  pn := fun _ _ _ _ _ _ => 0
  pnK := fun _ _ _ _ _ _ => 0
  mSmooth := fun _ _ _ _ => True
  mPsh := fun _ _ _ _ _ => True
  redZero := fun _ _ _ _ _ => True
  agreeOn := fun _ _ _ _ _ _ => True
  resNorm := by intros; exact 0
  Adl := fun _ => PUnit
  ofW := fun _ _ _ _ => PUnit.unit
  twist := fun _ _ _ _ => PUnit.unit
  arTop := fun _ _ => 0
  arVol := fun _ _ => 0
  nefA := fun _ _ => True
  supInf := fun _ _ _ _ _ => 0
  supFin := fun _ _ _ _ _ => 0
  cutGood := by intros; exact True
  cutHt := by intros; exact 0
  cutOrd := by intros; exact 0
  resFull := by intros; exact True
  resDeg := by intros; exact 0
  supInf_ofW := by intros; simp
  supInf_twist := by intros; simp
  supFin_twist := by intros; simp
  regOn := fun _ _ _ _ _ => True

def ngJunk : NgPkg where
  NgC := fun _ => PUnit
  NgC_ne := fun _ => ⟨PUnit.unit⟩
  KF := fun _ _ => Empty
  kfNorm := fun k _ => k.elim

def cxJunk (Tau : Type) [Fintype Tau] (N j : ℕ) : CxPkg Tau N j PUnit where
  Γ := fun _ => ⊥
  Γ_le := fun _ => bot_le
  volC := fun _ => 1
  volC_pos := fun _ => one_pos
  rfn := fun _ => Real.exp 1
  rfn_ge := fun _ => le_refl _
  hLo := fun _ => 1
  hUp := fun _ => 1
  hLo_le := fun _ => ⟨one_pos, le_refl _⟩
  connN := fun _ => 0
  curvN := fun _ => 0
  normDetInf := fun _ _ => 0

variable (D : D7)

def algJunk (N : ℕ) : AlgPkg (geoDegenerateNoTau D.what₂.LL) D.what₂.Tau N PUnit where
  Yv := fun _ => Formalism.DegreeFormula.dimFl D.what₂.Tau N
  Ybd := fun _ => PUnit.unit
  bd := fun _ => (0 : ℤ)
  bd_supp := fun _ => rfl
  Lw := fun _ => 0
  dim_eq := fun _ => rfl
  degA := fun _ _ => 0
  degA_ofW := fun _ _ _ _ => by simp [geoDegenerateNoTau]
  degA_twist := fun _ _ _ _ => rfl
  semipos := fun _ => True
  nefFib := fun _ => True
  Mbar := fun _ _ _ _ => PUnit.unit

def iThJunk (d : ℕ) : DV.ITh where
  LB := PUnit
  Ch := ℚ
  c1 := fun _ => 0
  VDiv := ℚ
  cD := 0
  capDeg := 0
  divP := 0
  cD_divP := rfl
  dim := d

def fpJunk (d r : ℕ) : DV.FPair (iThJunk d) r where
  x := fun _ => PUnit.unit
  x' := fun _ => PUnit.unit
  Dv := fun _ => 0
  hx := fun _ => by show (0 : ℚ) = 0 - (0 : ℚ →ₗ[ℚ] ℚ) 0; simp

theorem rkOf_dual {p : ℕ} [Fact p.Prime] (Ps : Set (DV.Emb D p)) (N j : ℕ) (hj : j ≤ N)
    (hPs : ∀ τ, τ ∈ Ps ↔ DV.cEmb D τ ∉ Ps) (τ : DV.Emb D p) :
    N - DV.rkOf Ps N j τ = DV.rkOf Ps N j (DV.cEmb D τ) := by
  classical
  unfold DV.rkOf
  by_cases h : τ ∈ Ps
  · have h' : DV.cEmb D τ ∉ Ps := (hPs τ).1 h
    simp [h, h']
  · have h' : DV.cEmb D τ ∈ Ps := by
      by_contra h''; exact h ((hPs τ).2 h'')
    simp [h, h']; omega

def mdlJunk (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ) (N j : ℕ) (hj : j ≤ N) :
    DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j) where
  Z := iThJunk (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1)
  cov := 1
  cov_pos := one_pos
  lvl := 0
  lie := fun _ => fpJunk _ _
  om := fun _ => fpJunk _ _
  lieW := fpJunk _ _
  omW := fpJunk _ _
  om_dual := fun τ => ⟨finCongr (rkOf_dual D _ N j hj (fun τ => _root_.Formalism.L2.Geo.cm_type_meets_conjugate_pair p jc τ) τ), fun _ => by show (0 : ℚ) = -0; rw [neg_zero]⟩
  dim_eq := rfl
  omW_dual := ⟨Equiv.refl _, fun _ => by show (0 : ℚ) = -0; rw [neg_zero]⟩

def padJunk (N j : ℕ) (hj : j ≤ N) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) :
    PadPkg D N j PUnit jC ngJunk where
  loc := fun p => junkLocalData D N j p
  ex := fun p => exJunk D N j p
  locB := fun p hp => junkLocB D N j p hp
  pbKF := fun _ _ k => Empty.elim k
  levIn := fun _ => True
  Xg := Empty
  bc := fun _ Z => Z.elim
  DivG := fun Z => Z.elim
  effD := @fun Z _ => Z.elim
  noVertD := @fun Z _ => Z.elim
  posBdD := @fun Z _ => Z.elim
  ampleOnAbelianBase := fun Z _ _ => Z.elim
  Met := Empty
  nefFibM := fun M => M.elim
  ampleGen := fun M => M.elim
  limRA := fun M => M.elim
  Mp := fun _ _ => PUnit
  md := fun p _ la _ => mdlJunk D p (jC p la) N j hj
  CurveM := fun _ _ _ => Empty
  degM := fun _ _ _ c => c.elim
  htMdl := fun _ _ => PUnit.unit
  Pt := Empty
  compPt := fun y => y.elim
  phiDR := fun _ y => y.elim
  phiMod := fun _ y => y.elim
  phiFr := fun _ y => y.elim
  phiFr_unram := fun _ y => y.elim
  normDetT := fun _ _ y => y.elim
  normDetH := fun _ _ y => y.elim
  htDetT := fun _ _ _ => 0
  arDeg := fun _ _ => 0
  arDeg_homog := fun _ _ _ _ _ _ => rfl
  arMix := fun _ _ _ => 0
  arMix_HT := fun _ _ _ _ => rfl
  arMix_DR := fun _ _ _ _ => rfl

section FlagZ

variable (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ)

def degFlZ (P : MvPolynomial (ι × Fin N) ℤ) : ℤ :=
  (-1) ^ Formalism.DegreeFormula.dimFl ι N *
    ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ))) * P.coeff (Formalism.DegreeFormula.permExp σ)

def linRootZ (lam : ι → Fin N → ℤ) : MvPolynomial (ι × Fin N) ℤ :=
  -∑ x : ι × Fin N, MvPolynomial.C (lam x.1 x.2) * MvPolynomial.X x

def flagDegZ (lam : ι → Fin N → ℤ) : ℤ := degFlZ ι N (linRootZ ι N lam ^ Formalism.DegreeFormula.dimFl ι N)

end FlagZ


open Classical in
@[reducible] def geoDegenerate (F : Type) [Field F] [NumberField F] [StarRing F] (Tau : Type) [Fintype Tau] : DV.Geo F where
  Var := ℕ
  dim := fun N => Formalism.DegreeFormula.dimFl Tau N
  Fn := fun _ => F
  fnField := fun _ => inferInstanceAs (Field F)
  fnAlg := fun _ => inferInstanceAs (Algebra F F)
  Dv := fun N => Tau → Fin N → ℤ
  dvGrp := fun _ => inferInstance
  Eff := fun _ _ => True
  eff_zero := fun _ => trivial
  eff_add := fun _ _ _ _ _ => trivial
  H0 := fun _ _ => ⊤
  degreeZeroCohomology_finiteDimensional := fun _ _ => inferInstance
  mul_mem_riemannRochSpace_add := fun _ _ _ _ _ _ _ => Submodule.mem_top
  riemannRoch_mono := fun _ _ _ _ => le_refl _
  KY := fun _ => 0
  Cl := fun _ => PUnit
  properCl := fun _ _ => True
  subCl := fun _ _ _ => True
  supp := fun _ _ => PUnit.unit
  inter := fun N v => if h : 0 < Formalism.DegreeFormula.dimFl Tau N then flagDegZ Tau N (v ⟨0, h⟩) else flagDegZ Tau N 0
  nef := fun _ _ => True
  big := fun _ _ => True
  bpf := fun _ _ _ => True
  phiBir := fun _ _ _ => True
  phiNoContr := fun _ _ _ _ => True
  vanishOn := fun _ _ _ _ => True
  hdim := fun _ _ _ => 0
  pts := fun _ _ => PUnit
  ptsMeas := fun _ _ => ⊤
  vol := fun _ _ => 0
  FnC := fun _ _ => ℂ
  fnCRing := fun _ _ => inferInstanceAs (CommRing ℂ)
  fnCAlg := fun _ _ => inferInstanceAs (Algebra ℂ ℂ)
  cx := fun _ σ => σ
  cx_smul := fun _ σ a f => by
    show σ (a * f) = σ a * σ f
    exact map_mul σ a f
  Met := fun _ _ _ => PUnit
  mAdd := fun _ _ _ _ _ _ => PUnit.unit
  mPow := fun _ _ _ _ _ => PUnit.unit
  fsMet := by intros; exact PUnit.unit
  pn := fun _ _ _ _ _ _ => 0
  pnK := fun _ _ _ _ _ _ => 0
  mSmooth := fun _ _ _ _ => True
  mPsh := fun _ _ _ _ _ => True
  redZero := fun _ _ _ _ _ => True
  agreeOn := fun _ _ _ _ _ _ => True
  resNorm := by intros; exact 0
  Adl := fun N => Tau → Fin N → ℤ
  ofW := fun _ L _ _ => L
  twist := fun _ L _ _ => L
  arTop := fun _ _ => 0
  arVol := fun _ _ => 0
  nefA := fun _ _ => True
  supInf := fun _ _ _ _ _ => 0
  supFin := fun _ _ _ _ _ => 0
  cutGood := by intros; exact True
  cutHt := by intros; exact 0
  cutOrd := by intros; exact 0
  resFull := by intros; exact True
  resDeg := by intros; exact 0
  supInf_ofW := by intros; simp
  supInf_twist := by intros; simp
  supFin_twist := by intros; simp
  regOn := fun _ _ _ _ _ => True

def ng1 : NgPkg where
  NgC := fun _ => PUnit
  NgC_ne := fun _ => ⟨PUnit.unit⟩
  KF := fun _ _ => PUnit
  kfNorm := fun _ _ => 1

def rho2 (r : ℕ) : ℕ := if 2 ≤ r then 1 else 0

def loc2 (r j p : ℕ) : ModuliIntegralCharts.Loc D r j p := locT D r j p (cfJunk p) (rho2 r)

def ex2 (r j p : ℕ) : ModuliIntegralCharts.ExtA D (loc2 D r j p) := extT D r j p (cfJunk p) (rho2 r)

def localBasisTwo (r j p : ℕ) (hp : p.Prime) : BoundaryLocalData.LocB D (loc2 D r j p) :=
  locBT D r j p (cfJunk p) (rho2 r) (Or.inl hp.two_le) (by
    unfold rho2
    split_ifs with h
    · nlinarith [h]
    · simp)

def padDegenerate (N j : ℕ) (hj : j ≤ N) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) :
    PadPkg D N j PUnit jC ng1 where
  loc := fun p => loc2 D N j p
  ex := fun p => ex2 D N j p
  locB := fun p hp => localBasisTwo D N j p hp
  pbKF := fun p _ _ => (1 : (cfJunk p).C)
  levIn := fun _ => True
  Xg := PUnit
  bc := fun _ _ => ()
  DivG := fun _ => PUnit
  effD := @fun _ _ => True
  noVertD := @fun _ _ => True
  posBdD := @fun _ _ => True
  ampleOnAbelianBase := fun _ _ _ => True
  Met := PUnit
  nefFibM := fun _ => True
  ampleGen := fun _ => True
  limRA := fun _ => True
  Mp := fun _ _ => PUnit
  md := fun p _ la _ => mdlJunk D p (jC p la) N j hj
  CurveM := fun _ _ _ => PUnit
  degM := fun _ _ _ _ _ => 0
  htMdl := fun _ _ => PUnit.unit
  Pt := PUnit
  compPt := fun _ => PUnit.unit
  phiDR := fun _ _ _ => 1
  phiMod := fun _ _ _ => 0
  phiFr := fun _ _ _ => 1
  phiFr_unram := fun _ _ _ _ => rfl
  normDetT := fun _ _ _ => 1
  normDetH := fun _ _ _ => 1
  htDetT := fun _ _ _ => 0
  arDeg := fun _ _ => 0
  arDeg_homog := fun _ _ _ _ _ _ => rfl
  arMix := fun _ _ _ => 0
  arMix_HT := fun _ _ _ _ => rfl
  arMix_DR := fun _ _ _ _ => rfl

def algDegenerate (N : ℕ) : AlgPkg (geoDegenerate D.what₂.LL D.what₂.Tau) D.what₂.Tau N PUnit where
  Yv := fun _ => N
  Ybd := fun _ => PUnit.unit
  bd := fun _ => 0
  bd_supp := fun _ => rfl
  Lw := fun _ => AddMonoidHom.id _
  dim_eq := fun _ => rfl
  degA := fun _ L => ((geoDegenerate D.what₂.LL D.what₂.Tau).inter N (fun _ => L) : ℝ)
  degA_ofW := fun _ _ _ _ => rfl
  degA_twist := fun _ _ _ _ => rfl
  semipos := fun _ => True
  nefFib := fun _ => True
  Mbar := fun _ _ _ _ => 0

def shimUFl {Lev : Type} (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (w : Dat D Lev) :
    ShimU D (geoDegenerate D.what₂.LL D.what₂.Tau) jC ng1 w where
  Comp := PUnit
  cx := cxJunk D.what₂.Tau w.N w.j
  alg := algDegenerate D w.N
  pad := padDegenerate D w.N w.j w.j_le jC

section Ar

variable (Tau : Type) [Fintype Tau] (N : ℕ)

end Ar

def formsFl (KO : Type) [Field KO] [NumberField KO] (eO : 𝓞 KO ≃+* D.what₂.O) (kL : KO →+* D.what₂.LL)
    (kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x))
    (NW : ℕ → ℕ) (algW : ∀ j, AlgPkg (geoDegenerate D.what₂.LL D.what₂.Tau) D.what₂.Tau (NW j) PUnit.{1})
    (PtY : ℕ → ℕ → Type) (pt : ∀ j p, PtY j p) :
    FormsPkg D (geoDegenerate D.what₂.LL D.what₂.Tau) NW (fun _ => PUnit.{1}) algW PtY where
  KO := KO
  eO := eO
  kL := kL
  kL_eO := kL_eO
  Cusp := fun _ _ => KO
  cmp := fun _ _ _ =>
    { toFun := fun F => (kL F : D.what₂.LL)
      map_add' := fun F F' => map_add kL F F'
      map_smul' := fun a F => by
        show kL (a * F) = kL a * kL F
        exact map_mul kL a F }
  cmp_mem := fun _ _ _ _ => Submodule.mem_top
  cmp_cusp := fun _ _ _ _ => trivial
  cmp_span := fun j _ _ w s _ => by
    have hs : s = (s PUnit.unit : D.what₂.LL) • (fun (_ : PUnit.{1}) => (kL 1 : D.what₂.LL)) := by
      funext c
      cases c
      show (s PUnit.unit : D.what₂.LL) = (s PUnit.unit : D.what₂.LL) * kL 1
      rw [map_one, mul_one]
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  cmp_indep := fun j w {n} v hv => by
    have hn : n ≤ 1 := by
      have := hv.fintype_card_le_finrank
      simpa using this
    rcases Nat.lt_or_ge n 1 with h0 | h1
    · have : IsEmpty (Fin n) := ⟨fun i => absurd i.2 (by omega)⟩
      exact linearIndependent_empty_type
    · obtain rfl : n = 1 := le_antisymm hn h1
      refine linearIndependent_unique_iff.2 ?_
      intro h
      have h2 := congrFun h PUnit.unit
      have h3 : kL (v default) = 0 := h2
      exact hv.ne_zero default ((map_eq_zero_iff kL kL.injective).1 h3)
  mulC := fun _ _ _ F F' => F * F'
  cmp_mul := fun _ _ _ _ F F' => map_mul kL F F'
  supN := fun _ _ σ F => ‖σ F‖
  supN_nonneg := fun _ _ _ _ => norm_nonneg _
  supN_eq_zero := fun _ _ σ F => by rw [norm_eq_zero, map_eq_zero_iff σ σ.injective]
  supN_smul := fun _ _ σ a F => by
    show ‖σ (a * F)‖ = ‖σ a‖ * ‖σ F‖
    rw [map_mul, norm_mul]
  supN_add := fun _ _ σ F G => by
    show ‖σ (F + G)‖ ≤ ‖σ F‖ + ‖σ G‖
    rw [map_add (f := _)]; exact norm_add_le _ _
  l2NormAlt := fun _ _ σ F => ‖σ F‖
  l2Norm_nonneg_bis := fun _ _ _ _ => norm_nonneg _
  l2Norm_eq_zero_iff := fun _ _ σ F => by rw [norm_eq_zero, map_eq_zero_iff σ σ.injective]
  l2Norm_smul_alt := fun _ _ σ a F => by
    show ‖σ (a * F)‖ = ‖σ a‖ * ‖σ F‖
    rw [map_mul, norm_mul]
  l2Norm_add_le' := fun _ _ σ F G => by
    show ‖σ (F + G)‖ ≤ ‖σ F‖ + ‖σ G‖
    rw [map_add (f := _)]; exact norm_add_le _ _
  l2Norm_le_supNorm_alt := fun _ _ _ _ => le_rfl
  Cu := fun _ => PUnit.{1}
  Xc := fun j _ => Submodule.span (𝓞 D.host.E) (Set.range (Pi.basisFun D.host.E (Fin (WeightFamilies.rho D j))))
  Xc_lat := fun _ _ => Submodule.IsLattice.of_fg D.host.E (Submodule.fg_span (Set.finite_range _))
  FJt := fun _ _ _ _ => KO
  sg := fun _ _ _ _ => LinearMap.id
  Pt := fun _ _ => PUnit.{1}
  pt66 := fun j la _ => pt j _
  vAtC := fun _ la _ _ F => vEK la F
  vAtC_zero := fun _ la _ _ => vEK_zero la
  vAtC_ne_bot := fun _ la _ _ F => vEK_ne_bot la F
  vAtC_add := fun _ la _ _ F G => vEK_add la F G
  vAtC_smul := fun _ la _ _ a F ha => vEK_mul la ha F
  vAtC_mul := fun _ la _ _ _ F F' => by
    show vEK la (F * F') = vEK la F + vEK la F'
    by_cases hF : F = 0
    · rw [hF, zero_mul, vEK_zero, EReal.top_add_of_ne_bot (vEK_ne_bot la F')]
    · rw [vEK_mul la hF, vEK_of_ne la hF]
  thAll := fun _ _ => ⊥
  shortTh := fun _ _ => ⊥

section Tied

variable (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))

def shimXJunk (N j : ℕ) (h1 : 1 ≤ j) (h2 : j < N) : DV.ShimX D.what₂.Tau where
  N := N
  j := j
  j_pos := h1
  j_lt := h2
  lev := Finset.univ.image D.host.g
  lev_prime := fun p hp => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    exact D.host.g_prime i
  Comp := PUnit
  vol := (cxJunk D.what₂.Tau N j).vol
  chern := (cxJunk D.what₂.Tau N j).chern
  chern_homog := fun P d hd hP => chernOf_homog D.what₂.Tau N (cxJunk D.what₂.Tau N j).vol P d hd hP
  arDeg := (padJunk D N j h2.le jC).arDeg
  arDeg_homog := (padJunk D N j h2.le jC).arDeg_homog
  arMix := (padJunk D N j h2.le jC).arMix
  arMix_HT := (padJunk D N j h2.le jC).arMix_HT
  arMix_DR := (padJunk D N j h2.le jC).arMix_DR
  CurveHT := (padJunk D N j h2.le jC).CurveHT
  degHT := (padJunk D N j h2.le jC).degHT
  CurveDR := (padJunk D N j h2.le jC).CurveDR
  degDR := (padJunk D N j h2.le jC).degDR
  FibComp := (padJunk D N j h2.le jC).FibComp
  fibInBd := (padJunk D N j h2.le jC).fibInBd
  Pt := (padJunk D N j h2.le jC).Pt
  phiDR := (padJunk D N j h2.le jC).phiDR
  phiMod := (padJunk D N j h2.le jC).phiMod
  phiFr := (padJunk D N j h2.le jC).phiFr
  XC := (cxJunk D.what₂.Tau N j).XC
  rfn := (cxJunk D.what₂.Tau N j).rfn
  rfn_ge := (cxJunk D.what₂.Tau N j).rfn_ge
  hLo := (cxJunk D.what₂.Tau N j).hLo
  hUp := (cxJunk D.what₂.Tau N j).hUp
  hLo_le := (cxJunk D.what₂.Tau N j).hLo_le
  connN := (cxJunk D.what₂.Tau N j).connN
  curvN := (cxJunk D.what₂.Tau N j).curvN
  compOf := (cxJunk D.what₂.Tau N j).compOf
  normDetInf := (cxJunk D.what₂.Tau N j).normDetInf
  compPt := (padJunk D N j h2.le jC).compPt
  normDetT := (padJunk D N j h2.le jC).normDetT
  normDetH := (padJunk D N j h2.le jC).normDetH
  htDetT := (padJunk D N j h2.le jC).htDetT
  ALB := (algJunk D N).ALB
  arSelf := fun L => ∑ c, (algJunk D N).arSelfC L c
  arSelfC := (algJunk D N).arSelfC
  arSelf_sum := fun _ => rfl
  geo := fun L => ∑ c, (algJunk D N).geoC L c
  geoC := (algJunk D N).geoC
  geo_sum := fun _ => rfl
  arVol := (algJunk D N).arVol
  semipos := (algJunk D N).semipos
  nefFib := (algJunk D N).nefFib
  arNef := (algJunk D N).arNef
  Mbar := (algJunk D N).Mbar

def recN (S : letI := D.host.cmStar; HSpace D.host.E) : ℕ :=
  letI := D.host.cmStar; if 2 ≤ S.rank then S.rank else 2

def firstSignatureEntry (S : letI := D.host.cmStar; HSpace D.host.E) : ℕ :=
  letI := D.host.cmStar; (S.sig (DV.tauEmb D (D.eTau.symm 1))).1

def recJ (S : letI := D.host.cmStar; HSpace D.host.E) : ℕ :=
  if 1 ≤ firstSignatureEntry D S ∧ firstSignatureEntry D S < recN D S then firstSignatureEntry D S else 1

theorem two_le_recN (S) : 2 ≤ recN D S := by unfold recN; split_ifs <;> omega
theorem recJ_pos (S) : 1 ≤ recJ D S := by unfold recJ; split_ifs with h; exacts [h.1, le_rfl]
theorem recJ_lt (S) : recJ D S < recN D S := by
  unfold recJ; split_ifs with h; exacts [h.2, two_le_recN D S]

theorem recN_dat {Lev : Type} (w : Dat D Lev) : recN D w.S = w.N := by
  unfold recN; rw [if_pos w.two_le]; rfl

theorem recJ_dat {Lev : Type} (w : Dat D Lev) (h : w.Indef) : recJ D w.S = w.j := by
  have e : firstSignatureEntry D w.S = w.j := by unfold firstSignatureEntry; rw [w.hsig]
  unfold recJ; rw [e, recN_dat, if_pos (show 1 ≤ w.j ∧ w.j < w.N from h)]

variable (X0 : DivX D)

def compatibleDivisorData : DivX D :=
  { X0 with
    geo := geoDegenerateNoTau D.what₂.LL
    Lev := Unit
    levPr := fun _ => Finset.univ.image D.host.g
    shv := fun S _ => shimXJunk D jC (recN D S) (recJ D S) (recJ_pos D S) (recJ_lt D S)
    shv_N := fun S _ h => by show recN D S = _; unfold recN; rw [if_pos h]
    shv_lev := fun _ _ => rfl
    PlP := fun p _ => PlL D p
    plpFin := fun p _ => finPl D p
    plpNe := fun p _ => plL_ne D p
    wtP := fun p _ => wtL D p
    divisorWeight_nonneg := fun p _ => wtL_nonneg D p
    divisorWeight_sum := fun p _ => wtL_sum D p
    plP := fun p _ => Formalism.BasicNotions.Examples₂.PlOver.plLEquiv D p
    divisorWeight_def := fun p _ la => Formalism.BasicNotions.Examples₂.PlOver.wtLog_eq D p la
    jC := fun p _ => jC p
    Mp := fun _ _ _ _ _ => PUnit
    md := fun S _ p _ la _ => mdlJunk D p (jC p la) (recN D S) (recJ D S) (recJ_lt D S).le
    phiFr_unram := fun _ _ _ y => Empty.elim y
    CurveM := fun _ _ _ _ _ _ => Empty
    degM := fun _ _ _ _ _ _ c => Empty.elim c
    htMdl := fun _ _ _ _ _ => PUnit.unit
    htCurve := fun _ _ _ _ => Equiv.refl _
    htCurve_deg := fun _ _ _ _ c => Empty.elim c.2
    Comp := fun _ => PUnit
    compFin := fun _ => inferInstance
    degHH := fun _ _ _ => 0
    Yv := fun j _ => Formalism.DegreeFormula.dimFl D.what₂.Tau (datW D () j).N
    Ybd := fun _ _ => PUnit.unit
    Lw := fun _ _ => 0
    iMj := fun j _ => (0 : (X0.MjH j).V →ₗ[D.what₂.LL] D.what₂.LL)
    iMj_mem := fun _ _ _ => by
      show (0 : D.what₂.LL) ∈ (⊥ : Submodule D.what₂.LL D.what₂.LL)
      exact Submodule.zero_mem _ }

theorem md_heq (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ) {N j N' j' : ℕ} (h h') (hN : N = N') (hj : j = j') :
    HEq (fun _ : PUnit.{1} => mdlJunk D p jc N j h) (fun _ : PUnit.{1} => mdlJunk D p jc N' j' h') := by
  subst hN; subst hj; rfl

theorem prime_of_mem_image : ∀ (_ : Unit), ∀ p ∈ Finset.univ.image D.host.g, p.Prime := fun _ p hp => by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
  exact D.host.g_prime i


end Tied

section TiedFl

variable (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))

def shimXFl (N j : ℕ) (h1 : 1 ≤ j) (h2 : j < N) : DV.ShimX D.what₂.Tau where
  N := N
  j := j
  j_pos := h1
  j_lt := h2
  lev := Finset.univ.image D.host.g
  lev_prime := fun p hp => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    exact D.host.g_prime i
  Comp := PUnit
  vol := (cxJunk D.what₂.Tau N j).vol
  chern := (cxJunk D.what₂.Tau N j).chern
  chern_homog := fun P d hd hP => chernOf_homog D.what₂.Tau N (cxJunk D.what₂.Tau N j).vol P d hd hP
  arDeg := (padDegenerate D N j h2.le jC).arDeg
  arDeg_homog := (padDegenerate D N j h2.le jC).arDeg_homog
  arMix := (padDegenerate D N j h2.le jC).arMix
  arMix_HT := (padDegenerate D N j h2.le jC).arMix_HT
  arMix_DR := (padDegenerate D N j h2.le jC).arMix_DR
  CurveHT := (padDegenerate D N j h2.le jC).CurveHT
  degHT := (padDegenerate D N j h2.le jC).degHT
  CurveDR := (padDegenerate D N j h2.le jC).CurveDR
  degDR := (padDegenerate D N j h2.le jC).degDR
  FibComp := (padDegenerate D N j h2.le jC).FibComp
  fibInBd := (padDegenerate D N j h2.le jC).fibInBd
  Pt := (padDegenerate D N j h2.le jC).Pt
  phiDR := (padDegenerate D N j h2.le jC).phiDR
  phiMod := (padDegenerate D N j h2.le jC).phiMod
  phiFr := (padDegenerate D N j h2.le jC).phiFr
  XC := (cxJunk D.what₂.Tau N j).XC
  rfn := (cxJunk D.what₂.Tau N j).rfn
  rfn_ge := (cxJunk D.what₂.Tau N j).rfn_ge
  hLo := (cxJunk D.what₂.Tau N j).hLo
  hUp := (cxJunk D.what₂.Tau N j).hUp
  hLo_le := (cxJunk D.what₂.Tau N j).hLo_le
  connN := (cxJunk D.what₂.Tau N j).connN
  curvN := (cxJunk D.what₂.Tau N j).curvN
  compOf := (cxJunk D.what₂.Tau N j).compOf
  normDetInf := (cxJunk D.what₂.Tau N j).normDetInf
  compPt := (padDegenerate D N j h2.le jC).compPt
  normDetT := (padDegenerate D N j h2.le jC).normDetT
  normDetH := (padDegenerate D N j h2.le jC).normDetH
  htDetT := (padDegenerate D N j h2.le jC).htDetT
  ALB := (algDegenerate D N).ALB
  arSelf := fun L => ∑ c, (algDegenerate D N).arSelfC L c
  arSelfC := (algDegenerate D N).arSelfC
  arSelf_sum := fun _ => rfl
  geo := fun L => ∑ c, (algDegenerate D N).geoC L c
  geoC := (algDegenerate D N).geoC
  geo_sum := fun _ => rfl
  arVol := (algDegenerate D N).arVol
  semipos := (algDegenerate D N).semipos
  nefFib := (algDegenerate D N).nefFib
  arNef := (algDegenerate D N).arNef
  Mbar := (algDegenerate D N).Mbar

theorem shimXFl_congr {N j N' j' : ℕ} (h1 h2 h1' h2') (hN : N = N') (hj : j = j') :
    shimXFl D jC N j h1 h2 = shimXFl D jC N' j' h1' h2' := by
  subst hN; subst hj; rfl

theorem toShimX_fl {Lev : Type} (w : Dat D Lev) (h : w.Indef) (hl) :
    toShimX (shimUFl D jC w) h (Finset.univ.image D.host.g) hl = shimXFl D jC w.N w.j h.1 h.2 := rfl

def lwFl (j : ℕ) : (D.what₂.Tau → Fin D.R.r → ℤ) →+ (D.what₂.Tau → Fin (datW D () j).N → ℤ) where
  toFun la := fun τ i => la τ (Fin.cast (datW_N D () j) i)
  map_zero' := rfl
  map_add' _ _ := rfl

variable (X0 : DivX D)

def divXFl : DivX D :=
  { X0 with
    geo := geoDegenerate D.what₂.LL D.what₂.Tau
    Lev := Unit
    levPr := fun _ => Finset.univ.image D.host.g
    shv := fun S _ => shimXFl D jC (recN D S) (recJ D S) (recJ_pos D S) (recJ_lt D S)
    shv_N := fun S _ h => by show recN D S = _; unfold recN; rw [if_pos h]
    shv_lev := fun _ _ => rfl
    PlP := fun p _ => PlL D p
    plpFin := fun p _ => finPl D p
    plpNe := fun p _ => plL_ne D p
    wtP := fun p _ => wtL D p
    divisorWeight_nonneg := fun p _ => wtL_nonneg D p
    divisorWeight_sum := fun p _ => wtL_sum D p
    plP := fun p _ => Formalism.BasicNotions.Examples₂.PlOver.plLEquiv D p
    divisorWeight_def := fun p _ la => Formalism.BasicNotions.Examples₂.PlOver.wtLog_eq D p la
    jC := fun p _ => jC p
    Mp := fun _ _ _ _ _ => PUnit
    md := fun S _ p _ la _ => mdlJunk D p (jC p la) (recN D S) (recJ D S) (recJ_lt D S).le
    phiFr_unram := fun _ _ _ _ _ _ => rfl
    CurveM := fun _ _ _ _ _ _ => PUnit
    degM := fun _ _ _ _ _ _ _ _ => 0
    htMdl := fun _ _ _ _ _ => PUnit.unit
    htCurve := fun _ _ _ _ => Equiv.refl _
    htCurve_deg := fun _ _ _ _ _ => rfl
    Comp := fun _ => PUnit
    compFin := fun _ => inferInstance
    degHH := fun _ _ _ => 0
    Yv := fun j _ => (datW D () j).N
    Ybd := fun _ _ => PUnit.unit
    Lw := fun j _ => lwFl D j
    iMj := fun j _ => (0 : (X0.MjH j).V →ₗ[D.what₂.LL] D.what₂.LL)
    iMj_mem := fun _ _ _ => Submodule.mem_top }

theorem degMFl_heq {N N' : ℕ} (hN : N = N') :
    HEq (fun (_ : PUnit.{1}) (_ : PUnit.{1}) (_ : DV.Rt D.what₂.Tau N) => (0 : ℝ))
      (fun (_ : PUnit.{1}) (_ : PUnit.{1}) (_ : DV.Rt D.what₂.Tau N') => (0 : ℝ)) := by
  subst hN; rfl

theorem tiedX_fl : TiedX (jC := jC) (ng := ng1) (divXFl D jC X0) (fun _ => Finset.univ.image D.host.g)
    (prime_of_mem_image D) () (fun p _ => Equiv.refl _) (fun w => shimUFl D jC w) (fun _ _ _ => Equiv.refl _) :=
  { shv :=
      { lev := rfl
        shv := fun w h => (shimXFl_congr D jC _ _ _ _ (recN_dat D w) (recJ_dat D w h)).trans
          (toShimX_fl D jC w h _).symm }
    pl :=
      { wt := fun _ _ _ => rfl
        jc := fun _ _ _ => rfl
        mp := fun _ _ _ _ _ => rfl
        md := fun w h p _ la => md_heq D p (jC p la) (recJ_lt D w.S).le w.j_le (recN_dat D w) (recJ_dat D w h)
        curveM := fun _ _ _ _ _ => HEq.rfl
        degM := fun w _ _ _ _ => degMFl_heq D (recN_dat D w)
        htMdl := fun _ _ _ _ _ => HEq.rfl
        htCurve := fun w h p _ c c' hc => by
          have e : c = c' := eq_of_heq hc
          subst e
          exact ⟨rfl, HEq.rfl⟩ }
    geo :=
      { yv := fun _ _ _ _ => rfl
        ybd := fun _ _ _ _ => HEq.rfl
        lw := fun _ _ _ _ _ => HEq.rfl }
    lev_κg := rfl }


end TiedFl

end Formalism.L2.Geo
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.LatticeGeometry.Inhabited =====

-- ===== clump member: Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP =====
-- clump-header: {"m": "Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP", "h": "module\n\npublic import Formalism.LocalToGlobal.LatticeGeometry.Inhabited\npublic import Formalism.LocalToGlobal.LatticeGeometry.LevPrPrime\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.Geo

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

def InPW (p : ℕ) [Fact p.Prime] (a : DV.KW p) : Prop :=
  ∃ b : WittVector p (AlgebraicClosure (ZMod p)), algebraMap _ (DV.KW p) b = a ∧ b.coeff 0 = 0

def ComplexEmbeddingsCompatible (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p) (τ : DV.Emb D p) (e : D.host.E →+* D.what₂.LL),
    (jc p la).comp τ = D.what₂.embLL.comp e →
      ∀ x : 𝓞 D.host.E, (InPW p (τ (x : D.host.E)) ↔ la.1.valuation D.what₂.LL (e (x : D.host.E)) < 1)

def CuspTieX (X : DivX D) : Prop :=
  ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ (c : X.Comp j) (x : (X.MjH j).V),
    X.geo.vanishOn (X.Yv j c) (X.Lw j c (DV.kapW D j)) (X.iMj j c x) (X.Ybd j c)

def IsoSp (S S' : letI := D.host.cmStar; HSpace D.host.E) : Prop :=
  letI := D.host.cmStar
  ∃ ι : S.V ≃ₗ[D.host.E] S'.V, HSpace.IsIsomEmb S S' ι.toLinearMap ∧
    S.L0.map (ι.toLinearMap.restrictScalars (𝓞 D.host.E)) = S'.L0

theorem IsoSp.rank_eq {S S' : letI := D.host.cmStar; HSpace D.host.E} (h : IsoSp S S') :
    (letI := D.host.cmStar; S.rank) = (letI := D.host.cmStar; S'.rank) := by
  obtain ⟨ι, -, -⟩ := h
  letI := D.host.cmStar
  rw [← S.rank_eq, ← S'.rank_eq]
  exact ι.finrank_eq

def IsoInv (F : ShimFam D G Lev) : Prop :=
  ∀ (w w' : Dat D Lev), IsoSp w.S w'.S → w.κ = w'.κ → w.j = w'.j → ∀ (h : w.Indef) (h' : w'.Indef),
    toShimX (F.U w) h (F.levPr w.κ) (F.levPr_prime w.κ) = toShimX (F.U w') h' (F.levPr w'.κ) (F.levPr_prime w'.κ)

def LevInTie (F : ShimFam D G Lev) (inK : Lev → ℕ → Prop) : Prop :=
  ∀ (w : Dat D Lev) (M : ℕ), (F.U w).pad.levIn M ↔ inK w.κ M

def GeoTiedP (X : DivX D) (inK : X.Lev → ℕ → Prop) : Prop :=
  ∃ (F : ShimFam D X.geo X.Lev) (ePl : ∀ (p : ℕ) [Fact p.Prime], X.PlP p ≃ PlL D p)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (F.U (datW D F.κg j)).Comp),
    TiedX (jC := F.jC) (ng := F.ng) X F.levPr F.levPr_prime F.κg ePl F.U eC ∧ ComplexEmbeddingsCompatible F.jC ∧ CuspTieX X ∧
      IsoInv F ∧ LevInTie F inK

variable (D)

def famFlJ (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (KO : Type) [Field KO] [NumberField KO]
    (eO : 𝓞 KO ≃+* D.what₂.O) (kL : KO →+* D.what₂.LL) (kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x)) :
    ShimFam D (geoDegenerate D.what₂.LL D.what₂.Tau) PUnit where
  levPr := fun _ => Finset.univ.image D.host.g
  levPr_prime := fun _ p hp => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    exact D.host.g_prime i
  κg := PUnit.unit
  levPr_κg := rfl
  jC := jc
  ng := ng1
  U := fun w => shimUFl D jc w
  forms := formsFl D KO eO kL kL_eO _ _ _ (fun _ _ => true)

theorem isoInv_famFlJ (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (KO : Type) [Field KO]
    [NumberField KO] (eO : 𝓞 KO ≃+* D.what₂.O) (kL : KO →+* D.what₂.LL)
    (kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x)) : IsoInv (famFlJ D jc KO eO kL kL_eO) := by
  intro w w' hiso _ hj h h'
  exact (toShimX_fl D jc w h _).trans ((shimXFl_congr D jc _ _ _ _ hiso.rank_eq hj).trans
    (toShimX_fl D jc w' h' _).symm)

theorem levInTie_famFlJ (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (KO : Type) [Field KO]
    [NumberField KO] (eO : 𝓞 KO ≃+* D.what₂.O) (kL : KO →+* D.what₂.LL)
    (kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x)) :
    LevInTie (famFlJ D jc KO eO kL kL_eO) (fun _ _ => True) :=
  fun _ _ => Iff.rfl

end Formalism.L2.Geo
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP =====
