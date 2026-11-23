module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureWeightSectionToTwistedPolarisationPower
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
theorem _root_.GlobalTheory.T.pureWeightSection_to_twistedPolarisationPower : (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N d : ℕ) (π : Φ.Pol N) (α : Φ.E.X), 1 ≤ N → 1 ≤ d → (∀ φ : (Φ.H d).Sec, Φ.Pure α φ → ∃ s : LB.Sec (Out.twistLB π.PB.A π.PB.L (N * d) (π.c α)), ((∀ j, s.f j = 0) → ∀ l, φ.f l = 0) ∧ ∀ x : Φ.Pt, (⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ ↔ ⊤ ≤ (Out.ptSecT π.PB.A (x ≫ Φ.D.q ≫ π.β.hom)).left ⁻¹ᵁ Out.nonzeroLocus s)) ∧ ∀ s : LB.Sec (Out.twistLB π.PB.A π.PB.L (N * d) (π.c α)), ∃ φ : (Φ.H d).Sec, Φ.Pure α φ ∧ ∀ x : Φ.Pt, (⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ ↔ ⊤ ≤ (Out.ptSecT π.PB.A (x ≫ Φ.D.q ≫ π.β.hom)).left ⁻¹ᵁ Out.nonzeroLocus s)) := by
  first | exact @GlobalTheory.ZH.TwSec.pure_sec_twist | exact GlobalTheory.ZH.TwSec.pure_sec_twist | (intros; apply GlobalTheory.ZH.TwSec.pure_sec_twist <;> assumption)
