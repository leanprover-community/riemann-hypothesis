module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartShortOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PIW.AdelClassFin

open NumberField

theorem successive_vector_basis : SvBasis := by
  intro E _ _ m M hfg hspan
  classical
  let M' : Submodule ℤ (Fin m → E) := M.restrictScalars ℤ
  have hfg' : M'.FG := hfg.restrictScalars
  have : Module.Finite ℤ M' := Module.Finite.iff_fg.2 hfg'
  have : Module.Free ℤ M' := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ M'
  let e0 : Module.Free.ChooseBasisIndex ℤ M' → Fin m → E := fun i => (b i : Fin m → E)
  have hli : LinearIndependent ℤ e0 := b.linearIndependent.map' M'.subtype (Submodule.ker_subtype _)
  have hliQ : LinearIndependent ℚ e0 := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hrep : ∀ x (hx : x ∈ M), x = ∑ i, (b.repr ⟨x, hx⟩ i) • e0 i := by
    intro x hx
    have h1 := congrArg Subtype.val (b.sum_repr (⟨x, hx⟩ : M')).symm
    rw [Submodule.coe_sum] at h1
    simpa only [Submodule.coe_smul] using h1
  have hmemM : ∀ x ∈ M, x ∈ Submodule.span ℚ (Set.range e0) := by
    intro x hx
    rw [hrep x hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hstab : ∀ c : E, ∀ v ∈ Submodule.span ℚ (Set.range e0), c • v ∈ Submodule.span ℚ (Set.range e0) := by
    intro c v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      obtain ⟨y, hy0, hyi⟩ := IsAlgebraic.exists_integral_multiple ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c))
      let α : 𝓞 E := ⟨y • c, hyi⟩
      have hαv : α • e0 i ∈ M := M.smul_mem α (b i).2
      have hyQ : (y : ℚ) ≠ 0 := Int.cast_ne_zero.2 hy0
      have : c • e0 i = ((y : ℚ)⁻¹) • (α • e0 i) := by
        have hα : (α • e0 i) = ((y : E) * c) • e0 i := by
          rw [Algebra.smul_def (A := E)] at *
          show ((y • c : E)) • e0 i = _
          rw [zsmul_eq_mul]
        rw [hα, mul_smul, ← smul_assoc]
        rw [show ((y : ℚ)⁻¹ • ((y : E))) = (1 : E) by
          rw [Algebra.smul_def, map_inv₀, map_intCast, inv_mul_cancel₀ (Int.cast_ne_zero.2 hy0)]]
        rw [one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (hmemM _ hαv)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  have hspanQ : Submodule.span ℚ (Set.range e0) = ⊤ := by
    let W : Submodule E (Fin m → E) :=
      { toAddSubmonoid := (Submodule.span ℚ (Set.range e0)).toAddSubmonoid
        smul_mem' := fun c v hv => hstab c v hv }
    have hle : Submodule.span E (M : Set (Fin m → E)) ≤ W := Submodule.span_le.2 fun x hx => hmemM x hx
    rw [hspan] at hle
    rw [eq_top_iff]
    intro v _
    exact hle (Submodule.mem_top)
  let B : Module.Basis (Module.Free.ChooseBasisIndex ℤ M') ℚ (Fin m → E) :=
    Module.Basis.mk hliQ (by rw [hspanQ])
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M') = m * Module.finrank ℚ E := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_pi_fintype]
    simp
  let σ : Fin (m * Module.finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ M' := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨e0 ∘ σ, hliQ.comp σ σ.injective, fun i => (b (σ i)).2, fun x hx => ?_⟩
  refine ⟨fun i => b.repr ⟨x, hx⟩ (σ i), ?_⟩
  conv_lhs => rw [hrep x hx]
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  rfl

end PIW.AdelClassFin

end
