module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationTransportEquiv
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.filtration_transport_equiv : ∀ {G H : Type} [Group G] [Group H] (ψ : H →* G) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ H V) (ρ' : Representation ℂ G V'), ρ.Equiv (ρ'.comp ψ) → ∀ (K : ℕ) (X : Fin K → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (τ : ∀ j, Representation ℂ G (X j)) (Vf : ℕ → Submodule ℂ V'), Vf 0 = ⊥ → Vf K = ⊤ → Monotone Vf → ∀ (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ' g)), (∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap (ρ'.subrepresentation (Vf (j + 1)) (hV (j + 1))) (τ j), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : V') ∈ Vf j) → ∃ S : Fin (K + 1) → Subrepresentation ρ, Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last K) = ⊤ ∧ ∀ t : Fin K, Nonempty ((GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)).Equiv ((τ t).comp ψ)) := by
  exact @GlobalTheory.CompanionTheory.FiltTransfer.subQuot_of_filtration
