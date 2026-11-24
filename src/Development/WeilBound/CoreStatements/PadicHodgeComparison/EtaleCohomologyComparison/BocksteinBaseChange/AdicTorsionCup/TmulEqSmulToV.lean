module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option backward.isDefEq.respectTransparency false


noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem gen_tmul_smul {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (a : ℤ_[l]) (y : N) :
    (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (a • y) = algebraMap ℤ_[l] ℚ_[l] a • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) := by
  rw [tmul_smul, algebraMap_smul]

theorem gen_tmul_eq {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (y : N) :
    c ⊗ₜ[ℤ_[l]] y = c • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) := by
  rw [smul_tmul', smul_eq_mul, mul_one]

theorem toV_smul (M : Model l K) (n : ℕ) (a : ℤ_[l]) (x : M.T n) :
    M.toV n (a • x) = algebraMap ℤ_[l] ℚ_[l] a • M.toV n x :=
  gen_tmul_smul (N := Hl l M.spc n 0) a x

theorem tmul_eq_smul_toV (M : Model l K) (n : ℕ) (c : ℚ_[l]) (x : M.T n) :
    (c ⊗ₜ[ℤ_[l]] (show Hl l M.spc n 0 from x) : M.V n) = c • M.toV n x :=
  gen_tmul_eq (N := Hl l M.spc n 0) c x

theorem pull_gal_inj (M : Model l K) (n : ℤ) (τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (x : Hl l M.spc n 0)
    (h : pullHl l (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q τ)) n 0 x = 0) : x = 0 := by
  have e := congrArg (pullHl l (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q τ⁻¹)) n 0) h
  rw [← LinearMap.comp_apply, ← pullHl_comp, ← Functor.map_comp, ← galMap_mul, inv_mul_cancel, galMap_one,
    CategoryTheory.Functor.map_id, pullHl_id, map_zero] at e
  exact e

theorem pull_comp_apply {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) (x : Hl l E'' n i) :
    pullHl l (f ≫ g) n i x = pullHl l f n i (pullHl l g n i x) := by
  rw [pullHl_comp]; rfl

end CrystallineSemistableComparison.AdicCoh
