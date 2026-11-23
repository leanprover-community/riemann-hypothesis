module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicProperties
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : ResEtaPow (R := F) ⊥ χ m), sc F χ m 1 = 1 ∧ (∀ z z' : E, sc F χ m (z * z') = sc F χ m z * sc F χ m z') ∧ (∀ z : Eˣ, sc F χ m (z : E) = (χ z : ℂ) * ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) ∧ (∀ z : Eˣ, ‖sc F χ m (z : E)‖ ^ 2 = nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m) ∧ (∀ z : Eˣ, sc F χ m (c (z : E))⁻¹ * ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) = sc F χ m (z : E)) ∧ (∀ t : Fˣ, sc F χ m (algebraMap F E t) = (sgn E t * (nabs F t : ℝ)) ^ m) ∧ ∀ z : Eˣ, sc F χ m ((z : E) * c (z : E)) = ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) := by
  first | exact @GlobalTheory.KSp.sc_basic | exact GlobalTheory.KSp.sc_basic | (intros; apply GlobalTheory.KSp.sc_basic <;> assumption)
