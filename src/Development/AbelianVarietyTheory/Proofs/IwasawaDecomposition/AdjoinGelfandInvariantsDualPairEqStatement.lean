module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdjoinGelfandInvariantsDualPairEq
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.Mem.Lift

theorem _root_.GlobalTheory.T.adjoin_gelfandInvariants_dual_pair_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → ∀ c c' : ℂ, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)) = Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)) := by
  first | exact @GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair | exact GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair | (intros; apply GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair <;> assumption)
