module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsThetaShiftTriple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_integral_sections_thetaShift_triple : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (Dd : DegData R (maximalIdeal R)) (k : ℕ), 1 ≤ k → ∀ (mu mu' α : Dd.toPre.X), ∃ (σ : Dd.toPre.SecB k α) (σ₁ : Dd.toPre.SecB k (α + k • mu)) (σ₂ : Dd.toPre.SecB k (α + k • mu + k • mu')) (e : Dd.toPre.SecB k (α + k • mu + k • mu') = Dd.toPre.SecB k (α + k • (mu + mu'))), ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ ∧ ShiftEq Dd.toPre k mu' (α + k • mu) σ₁ σ₂ 0 σ₂ ∧ ShiftEq Dd.toPre k (mu + mu') α σ (cast e σ₂) 0 (cast e σ₂) ∧ ∃ (z : (DegPre.BF Dd.toPre (FractionRing R)).left) (J : ((DegPre.BF Dd.toPre (FractionRing R)).left ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J ∧ IsUnit (sval σ (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J) := by
  first | exact @GlobalTheory.IntegralFamTriple.exists_triple | exact GlobalTheory.IntegralFamTriple.exists_triple | (intros; apply GlobalTheory.IntegralFamTriple.exists_triple <;> assumption)
