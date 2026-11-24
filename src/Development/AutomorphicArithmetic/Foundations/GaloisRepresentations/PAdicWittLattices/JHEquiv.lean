module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHEquiv :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv := by
  intro k k' _ _ _ J e M N M₀ N₀ _ _ _ _ _ _ _ _ ψ E E' ψ₀ h hψ
  let R : (J →₀ M₀) ≃+ (J →₀ M) := Finsupp.mapRange.addEquiv E.toAddEquiv
  have key : ∀ f : J →₀ M₀, bcSum e ψ₀ f = E' (bcSum e ψ (R f)) := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hf, hg]
    | single j m =>
      simp only [R, Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_single]
      rw [bcSum_single, bcSum_single, h, map_smul]
      rfl
  have hfun : ⇑(bcSum e ψ₀) = ⇑E' ∘ ⇑(bcSum e ψ) ∘ ⇑R := funext key
  show Function.Bijective ⇑(bcSum e ψ₀)
  rw [hfun]
  exact E'.bijective.comp (hψ.comp R.bijective)
