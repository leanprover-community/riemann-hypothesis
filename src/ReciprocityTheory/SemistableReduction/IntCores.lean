module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.IntCoresB

@[expose] public section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory MvPolynomial

def blockSlice {B n : ℕ} (b : Fin B) (p : Fin B → Fin n → ℂ) :
    Fin B × Fin n → MvPolynomial (Fin n) ℂ :=
  fun q => if q.1 = b then X q.2 else C (p q.1 q.2)

theorem blockSlice_isHomogeneous {B n : ℕ} {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin n) ℂ}
    (hf : IsMultiHomogeneous a f) (b : Fin B) (p : Fin B → Fin n → ℂ) :
    (bind₁ (blockSlice b p) f).IsHomogeneous (a b) := by

  rw [f.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro s hs
  rw [bind₁_monomial]
  have hdeg : ∀ q, (blockSlice b p q).IsHomogeneous (if q.1 = b then 1 else 0) := by
    intro q; unfold blockSlice; split_ifs
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_C _ _
  have hprod := IsHomogeneous.prod s.support (fun q => blockSlice b p q ^ s q)
    (fun q => (if q.1 = b then 1 else 0) * s q) (fun q _ => (hdeg q).pow (s q))
  have hsum : ∑ q ∈ s.support, (if q.1 = b then 1 else 0) * s q = a b := by
    rw [Finset.sum_subset (Finset.subset_univ _)
      (fun q _ hq => by simp [Finsupp.notMem_support_iff.1 hq])]
    rw [← hf s hs b, Fintype.sum_prod_type]
    simp [ite_mul]
  rw [← zero_add (a b), ← hsum]
  exact (isHomogeneous_C _ _).mul hprod

theorem eval_blockSlice {B n : ℕ} (f : MvPolynomial (Fin B × Fin n) ℂ) (b : Fin B)
    (p : Fin B → Fin n → ℂ) (w : Fin n → ℂ) :
    eval w (bind₁ (blockSlice b p) f) = eval (fun q => Function.update p b w q.1 q.2) f := by
  have hφ : (fun q => eval₂Hom (RingHom.id ℂ) w (blockSlice b p q)) =
      fun q => Function.update p b w q.1 q.2 := by
    funext q
    by_cases hq : q.1 = b
    · simp [blockSlice, hq]
    · simp [blockSlice, hq]
  show eval₂Hom (RingHom.id ℂ) w (bind₁ _ f) = _
  rw [eval₂Hom_bind₁, hφ]
  rfl

theorem sphereLogIntegrable_holds (hSJ : SJStatement) : SphereLogIntegrableStatement := by
  intro B n a f _ hf
  set F : (Fin B → Fin n → ℂ) → ℂ := fun p => eval (fun q => p q.1 q.2) f with hFdef
  have hF : BlockPoly B n a F := by
    refine ⟨(continuous_eval f).comp (continuous_pi fun q =>
      (continuous_apply q.2).comp (continuous_apply q.1)), fun b p => ?_⟩
    exact ⟨_, blockSlice_isHomogeneous hf b p, fun w => (eval_blockSlice f b p w).symm⟩
  by_cases hz : ∃ z0, onSpheres F z0 ≠ 0
  · obtain ⟨z0, hz0⟩ := hz
    exact (blockPoly_claim hSJ n B a F hF z0 hz0).1
  · simp only [not_exists, not_not] at hz
    have : (fun z : BlockSphere B n => Real.log ‖eval (blockPoint z) f‖) = fun _ => 0 := by
      funext z
      have h0 : eval (blockPoint z) f = 0 := hz z
      rw [h0, norm_zero, Real.log_zero]
    rw [this]
    exact integrable_zero _ _ _

end ReciprocityTheory.MultiplicativeHeights
