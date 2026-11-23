module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.continuous_twoCocycle_multiple_of_fundamental : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (χ : G →* ℤ_[l]ˣ) (c : G × G → ℤ_[l]), Continuous (fun g => (χ g : ℤ_[l])) → (∀ r, GlobalTheory.TateTop.Gen χ r c) → (∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)))) → (Continuous (fun p => (c p : ℚ_[l])) ∧ ∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * (c (h, k) : ℚ_[l]) - (c (g * h, k) : ℚ_[l]) + (c (g, h * k) : ℚ_[l]) - (c (g, h) : ℚ_[l]) = 0) ∧ ∀ z : G × G → ℚ_[l], Continuous z → (∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ (x : ℚ_[l]) (f : G → ℚ_[l]), Continuous f ∧ ∀ g h, ((χ g : ℤ_[l]) : ℚ_[l]) * f h - f (g * h) + f g = z (g, h) - x * (c (g, h) : ℚ_[l]) := by
  first | exact @GlobalTheory.GenSpan.span | exact GlobalTheory.GenSpan.span | (intros; apply GlobalTheory.GenSpan.span <;> assumption)
