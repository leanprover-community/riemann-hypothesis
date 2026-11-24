module

public import Formalism.DistinguishedUnitIdeals.ExistsConstOfInvariantMod
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Graded
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.ArcParametersShiftInvariant
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

section Free

variable {LL D ι : Type} [Field LL] [AddCommGroup D] [Module LL D] [Fintype ι] [DecidableEq ι]

def evK (i : ι) : (ι → LL) ⊗[LL] D →ₗ[LL] D :=
  (TensorProduct.lid LL D).toLinearMap ∘ₗ LinearMap.rTensor D (LinearMap.proj i)

theorem evaluation_tmul (i : ι) (b : ι → LL) (d : D) : evK i (b ⊗ₜ[LL] d) = b i • d := by
  simp [evK]

theorem evaluation_smul (i : ι) (a : ι → LL) (z : (ι → LL) ⊗[LL] D) :
    evK i (a • z) = a i • evK i z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b d =>
    rw [TensorProduct.smul_tmul', evaluation_tmul, evaluation_tmul, smul_eq_mul, Pi.mul_apply,
      mul_smul]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem tensor_sum_single_eval (z : (ι → LL) ⊗[LL] D) :
    z = ∑ i, (Pi.single i (1 : LL) : ι → LL) ⊗ₜ[LL] evK i z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b d =>
    have hb : ∑ i, b i • (Pi.single i (1 : LL) : ι → LL) = b := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    simp_rw [evaluation_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, hb]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem mem_baseChange_iff (X : Submodule LL D) (z : (ι → LL) ⊗[LL] D) :
    z ∈ X.baseChange (ι → LL) ↔ ∀ i, evK i z ∈ X := by
  constructor
  · intro h i
    have h' : z ∈ Submodule.span (ι → LL)
        ((X.map (TensorProduct.mk LL (ι → LL) D 1) : Submodule LL _) : Set ((ι → LL) ⊗[LL] D)) := by
      rw [← Submodule.baseChange_eq_span]; exact h
    clear h
    induction h' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      simpa [evaluation_tmul] using hm
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact X.add_mem hx hy
    | smul a x _ hx => rw [evaluation_smul]; exact X.smul_mem _ hx
  · intro h
    rw [tensor_sum_single_eval z]
    exact Submodule.sum_mem _ fun i _ => Submodule.tmul_mem_baseChange_of_mem _ (h i)

theorem xi_iff (X : ℤ → Submodule LL D) (f : Amb LL (ι → LL) D) :
    f ∈ Xi (ι → LL) X ↔ ∀ i k, evK i (cf f k) ∈ X k := by
  change (∀ k, cf f k ∈ (X k).baseChange (ι → LL)) ↔ _
  simp only [mem_baseChange_iff]
  exact forall_comm

theorem xi_unit_tp (X : ℤ → Submodule LL D) (hX : Monotone X) (a b : PowerSeries (ι → LL)) (hab : a * b = 1)
    (g : ℤ) (f : Amb LL (ι → LL) D) :
    (HahnSeries.ofPowerSeries ℤ (ι → LL) a * tp (ι → LL) g) • f ∈ Xi (ι → LL) X ↔
      f ∈ Xi (ι → LL) (fun i => X (i + g)) := by
  rw [mul_smul, ← xi_shift_holds LL (ι → LL) D X g f]
  constructor
  · intro h
    have h2 := xi_module_structure LL (ι → LL) D X hX b _ h
    rwa [← mul_smul, ← map_mul, show b * a = 1 by rw [mul_comm]; exact hab, map_one, one_smul] at h2
  · intro h
    exact xi_module_structure LL (ι → LL) D X hX a _ h

end Free

end Formalism.MainNotions.N.Ln03.K8
