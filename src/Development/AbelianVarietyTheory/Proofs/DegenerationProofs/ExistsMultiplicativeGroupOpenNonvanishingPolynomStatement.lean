module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMultiplicativeGroupOpenNonvanishingPolynom
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

theorem _root_.GlobalTheory.T.exists_multiplicativeGroup_open_nonvanishing_polynomial : ∀ (k : Type) [Field k] (q : Polynomial k), ∃ jj : algOver k (Localization.Away (Polynomial.X * q)) ⟶ Gm (Sp k), IsOpenImmersion jj.left ∧ ∀ x y z : Localization.Away (Polynomial.X * q) →ₐ[k] k, (algOverHom x ≫ jj) * (algOverHom y ≫ jj) = algOverHom z ≫ jj → x (algebraMap (Polynomial k) _ Polynomial.X) * y (algebraMap (Polynomial k) _ Polynomial.X) = z (algebraMap (Polynomial k) _ Polynomial.X) := by
  first | exact @GlobalTheory.SS.TorOpen.exists_open_part | exact GlobalTheory.SS.TorOpen.exists_open_part | (intros; apply GlobalTheory.SS.TorOpen.exists_open_part <;> assumption)
