module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFirstCohomologyComparison
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.USt

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.product_first_cohomology_comparison : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (P : Type) [SemilatticeInf P] (S : Sys A.left P),
    ∃ (Q : Type) (_ : SemilatticeInf Q) (S' : Sys (A ⊗ A).left Q)
      (m : CoefMap (RingHom.id R) (box (OSys A.hom S)) (OSys (A ⊗ A).hom S')),
      Function.Surjective m.pull1 ∧
      (∀ x c, IsPullO (wOver (fst A A)) x c →
        (resSys _ S').pull1 c = m.pull1 ((boxL _).pull1 ((resSys _ S).pull1 x))) ∧
      (∀ x c, IsPullO (wOver (snd A A)) x c →
        (resSys _ S').pull1 c = m.pull1 ((boxR _).pull1 ((resSys _ S).pull1 x))) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_boxSys | exact GlobalTheory.CompanionTheory.Axis.exists_boxSys | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_boxSys <;> assumption)
