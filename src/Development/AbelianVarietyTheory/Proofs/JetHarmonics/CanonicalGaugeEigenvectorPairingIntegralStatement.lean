module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CanonicalGaugeEigenvectorPairingIntegral
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
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalGauge_eigenvector_pairing_integral : ∀ (R : Type) [CommRing R] (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d OE) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (σ : OE →+* R) (a0 : OE), IsUnit (σ a0 - σ (star a0)) → ∀ u u' : Fin d → R, (∀ a, (linPart (B.A.act a)).mulVec u = σ a • u) → (∀ a, (linPart (B.A.act a)).mulVec u' = σ a • u') → ∀ w : OE, dotProduct (fun i => algebraMap R k (u i)) ((ReciprocityTheory.ChartRestriction.G.TB.bilinPart k h).mulVec ((ReciprocityTheory.ChartRestriction.G.TB.dAct k B w).mulVec (fun i => algebraMap R k (u' i)))) ∈ (algebraMap R k).range := by
  first | exact @GlobalTheory.CharDepth.eigen_pair_mem_range | exact GlobalTheory.CharDepth.eigen_pair_mem_range | (intros; apply GlobalTheory.CharDepth.eigen_pair_mem_range <;> assumption)
