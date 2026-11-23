module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
public import GroundTheory.AutomorphicForms.ReductionHeight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEpsilonCentralizerBound
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.exists_epsilon_centralizer_bound : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K), (∀ y : Fin n → K, ∃ h : K[X], y = v ᵥ* aeval γ h) → ∀ e : Matrix (Fin n) (Fin n) K, IsPrim γ e → ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ g : GroundTheory.Automorphic.AdelicGLn.AdelicGL K n, g.val * γ.map (algebraMap K (AdeleRing (𝓞 K) K)) = γ.map (algebraMap K (AdeleRing (𝓞 K) K)) * g.val → ∀ s : (AdeleRing (𝓞 K) K)ˣ, (s : AdeleRing (𝓞 K) K) = (1 + e.map (algebraMap K (AdeleRing (𝓞 K) K)) * (g.val - 1)).det → c ≤ (GroundTheory.Global.IdeleGroup.ideleModule K s : ℝ) → ∀ x : Fin n → K, x ᵥ* e ≠ 0 → ε ≤ GroundTheory.Automorphic.Reduction.height g x := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.HeightBound.exists_pos_le_height | exact GlobalTheory.CompanionTheory.TorusCh.HeightBound.exists_pos_le_height | (intros; apply GlobalTheory.CompanionTheory.TorusCh.HeightBound.exists_pos_le_height <;> assumption)
