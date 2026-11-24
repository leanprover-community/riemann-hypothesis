module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsBaseChangePolarisedDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstantsJets_baseChange_polarisedDatum : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (x : KeyIn R) (x' : KeyIn K) (φ : x'.P.A.left ⟶ x.P.A.left), KeyAtMap x' x f φ → ∀ (g : ℕ) (hg : x.P.g = g) (hg' : x'.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp R) ⟶ x.P.A)) (pt' : I → (baseOver (Sp K) ⟶ x'.P.A)) (ϑ : I → R) (J : I → Fin g → R), (∀ i, (pt' i).left ≫ φ = spMap f ≫ (pt i).left) → ThJet x hg m pt ϑ J → ThJet x' hg' m pt' (fun i => f (ϑ i)) (fun i j => f (J i j)) := by
  first | exact @GlobalTheory.MBLow.thJet_of_keyAtMap | exact GlobalTheory.MBLow.thJet_of_keyAtMap | (intros; apply GlobalTheory.MBLow.thJet_of_keyAtMap <;> assumption)
