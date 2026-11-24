module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePolynomialDefectBilinearAdditiveParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cocycle_polynomialDefect_bilinear_additive_parts : ∀ (R X : Type) [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup X] (w : X → X →+ R) (π π' : X → R), (∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α : X, 2 * (k : R) * w (mu + mu') α + 2 * (k : R) ^ 2 * π (mu + mu') + 2 * (k : R) * π' (mu + mu') = (2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) + (2 * (k : R) * w mu' (α + k • mu) + 2 * (k : R) ^ 2 * π mu' + 2 * (k : R) * π' mu')) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) ∧ (∀ mu mu', w mu mu' = w mu' mu) ∧ (∀ mu mu', π' (mu + mu') = π' mu + π' mu') ∧ ∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu := by
  first | exact @GlobalTheory.cocycle_polynomial_defect | exact GlobalTheory.cocycle_polynomial_defect | (intros; apply GlobalTheory.cocycle_polynomial_defect <;> assumption)
