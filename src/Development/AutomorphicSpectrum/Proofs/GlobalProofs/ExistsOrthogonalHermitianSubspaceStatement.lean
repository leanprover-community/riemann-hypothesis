module

public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsOrthogonalHermitianSubspace
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

open Matrix

theorem _root_.GlobalTheory.T.involution_stable_subspace_coordinate : ∀ {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), (∀ v ∈ W, Formalism.REAL.Jm ε *ᵥ v ∈ W) →
    ∃ (k : Formalism.REAL.KG ε) (S : Set (Fin n)),
      W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map (Formalism.REAL.toMK k).mulVecLin := by
  first | exact @GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate | exact GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate | (intros; apply GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate <;> assumption)
