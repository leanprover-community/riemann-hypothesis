module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : Mx k r), γ ∈ GG k r → (∀ F F' : Mx k r → (Wq →L[ℂ] Wp), (∀ g ∈ GG k r, F g = F' g) → B.JF D F γ = B.JF D F' γ ∧ (Integrable (JF.integrand D F γ) D.μSS → Integrable (JF.integrand D F' γ) D.μSS)) ∧ (∀ (φ : Mx k r → ℂ) (F : Mx k r → (Wq →L[ℂ] Wp)), (∀ p, D.inSS p → φ (B.sgs p γ) = φ γ) → B.JF D (fun g => φ g • F g) γ = φ γ • B.JF D F γ) ∧ (∀ (ι : Type) [Fintype ι] (F : ι → Mx k r → (Wq →L[ℂ] Wp)), (∀ i, Integrable (JF.integrand D (F i) γ) D.μSS) → B.JF D (fun g => ∑ i, F i g) γ = ∑ i, B.JF D (F i) γ) ∧ ∀ᵐ p ∂D.μSS, D.inSS p := by
  first | exact @GlobalTheory.BesselFunctionBasic.JF_basic | exact GlobalTheory.BesselFunctionBasic.JF_basic | (intros; apply GlobalTheory.BesselFunctionBasic.JF_basic <;> assumption)
