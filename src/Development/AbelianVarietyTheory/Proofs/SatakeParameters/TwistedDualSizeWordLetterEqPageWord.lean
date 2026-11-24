module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem recWord_letter_eq_pageWord : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ ψ : D.R.GG),
    Roomy L C → ∀ a : ZMod (orderOf ψ),
    (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) = (pageWord L j ε τ ψ).sz a ∧
    (recWord L j ε (letter τ ψ)).Mi a = (pageWord L j ε τ ψ).Mi a ∧
    (recWord L j ε (letter τ ψ)).hi a = (pageWord L j ε τ ψ).hi a ∧
    (ThickN (bHat L) (etaHat L) (recWord L j ε (letter τ ψ)).sz a ↔ (pageWord L j ε τ ψ).thick a) := by
  intro D L C j ε τ ψ hR a
  have hB := GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ ψ hR
  have hpos : (etaHat L : ℤ) < szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) := hB.2.2.2.2.2 a
  have h0 : 0 ≤ szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) := by omega
  have hc : ((szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a))).toNat : ℤ) =
      szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) := Int.toNat_of_nonneg h0
  have hS : (szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) + (sHat L : ℤ)).toNat =
      (szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a))).toNat + sHat L := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hc
  · simp only [recWord, pageWord, WordData.Mi, hS]
  · simp only [recWord, pageWord, WordData.hi, hS]
  · simp only [ThickN, recWord, pageWord, WordData.thick]
    omega

end GlobalTheory.HTW.Rec
