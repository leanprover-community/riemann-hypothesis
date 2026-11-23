module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockSource
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.NoLowPairing

theorem no_pairing_of_noLow : ∀ (X : ProvA) (p q r s : ℕ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds r s lam').HK → NoLow X p q lam' → ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q → ∀ b : Formalism.BasicNotions.TH.Pol (p - i) (q - i) r s →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] ℂ, (∀ Z ∈ upq r s, ∀ P y, b (fockAct2 (p - i) (q - i) r s Z P) y + b P ((X.ds r s lam').HK.act Z y) = 0) → b = 0 := by
  intro X p q r s lam' hadm hlow i hi hip hiq b hb
  exact GlobalTheory.NoInvPairing.eq_zero_of_noIntw' (X.ds r s lam') (X.fock (p - i) (q - i) r s) hadm
    (fun M f hf => hlow i hi hip hiq M f hf) b hb

end GlobalTheory.NoLowPairing
