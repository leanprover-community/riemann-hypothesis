module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniversalSectionBasisPolarisedFibre
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.exists_universal_section_basis_polarised_fibre : Laws2 → ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (P : PolAV S') (f : S' ⟶ S) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G f φ → LBIso P.L (L.pull φ) → ∀ (K : Type) [Field K] (y : Sp K ⟶ S') (x : Sp K ⟶ S), y ≫ f = x → ∃ e, UnivBasis G L x e := by
  first | exact @GlobalTheory.Ex.OneGen.exists_univBasis_of_fibre | exact GlobalTheory.Ex.OneGen.exists_univBasis_of_fibre | (intros; apply GlobalTheory.Ex.OneGen.exists_univBasis_of_fibre <;> assumption)
