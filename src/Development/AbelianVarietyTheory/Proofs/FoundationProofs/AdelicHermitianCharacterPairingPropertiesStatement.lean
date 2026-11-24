module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdelicHermitianCharacterPairingProperties
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.adelicHermitianCharacterPairing_properties : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ ψ : AE D → ℂ, IsPsi D cc δ ψ → ∀ (N N' : ℕ), (∀ u ζ η, gamA ψ (actA D N N' u ζ) (actA D N N' u η) = gamA ψ ζ η) ∧ (∀ ζ : XA D N N', gamA ψ ζ ζ = 1) ∧ (∀ (r : 𝓞 D.host.E) (ζ η : XA D N N'), gamA ψ (r • ζ) η = gamA ψ ζ (sgO D r • η)) ∧ (∀ ζ η ξ : XA D N N', gamA ψ (ζ + η) ξ = gamA ψ ζ ξ * gamA ψ η ξ) ∧ (∀ ζ η ξ : XA D N N', gamA ψ ζ (η + ξ) = gamA ψ ζ η * gamA ψ ζ ξ) := by
  first | exact @GlobalTheory.FinWeil.gamA_alg | exact GlobalTheory.FinWeil.gamA_alg | (intros; apply GlobalTheory.FinWeil.gamA_alg <;> assumption)
