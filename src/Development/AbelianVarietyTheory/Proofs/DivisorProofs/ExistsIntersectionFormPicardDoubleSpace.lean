module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_interForm_dbl : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∃ T : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (Y.dim + 1) => Pic W.Z) ℤ, (∀ (σ : Equiv.Perm (Fin (Y.dim + 1))) (y : Fin (Y.dim + 1) → Pic W.Z), T (y ∘ σ) = T y) ∧ ∀ y : Fin (Y.dim + 1) → CartierDiv W.Z, T (fun i => toPic (y i)) = W.num y := by
  intro F _ Y W hW
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hv : DiffVanish (Y.dim + 1 + 1) (chiPic F (structureModule W.Z)) :=
    diffVanish_chiPic_of_isProjOver (algebraΓOfHom_algebraMap (W.p₁ ≫ Y.str)) (structureModule W.Z) W.proj
      (by rw [GlobalTheory.QCoh.suppDim_structureModule]; exact hW)
  refine ⟨hv.form, fun σ y => hv.form_comp_perm y σ, fun y => ?_⟩
  rw [hv.form_apply _ 0]
  show _ = interNum F (structureModule W.Z) fun i => toLB (y i)
  rw [interNum_eq_multiDiff F _ fun i => isLB_toLB (y i)]
  rfl

end GlobalTheory.FlagPush
