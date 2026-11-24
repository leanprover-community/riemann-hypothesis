module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BorelHarishChandra
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.nsq_act_le_of_isSiegel_of_entries_zero_or_ge : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), (∀ C : ℝ, ∃ C' : ℝ, ∀ y : Matrix ι ι ℂ, y.det = 1 → nsq (act d v y) ≤ C → ∃ h : Matrix ι ι ℂ, h.det = 1 ∧ act d v h = v ∧ ∀ i j, ‖(h * y) i j‖ ≤ C') → (∀ g : Matrix ι ι ℂ, g.det = 1 → act d v g = v → act d v gᴴ = v) → ∀ C c : ℝ, 0 < c → ∃ C' : ℝ, ∀ (k : Matrix ι ι ℝ) (a : ι → ℝ) (n : Matrix ι ι ℝ), IsSiegel C k a n → (∀ j, act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ))) j = 0 ∨ c ≤ ‖act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ))) j‖) → nsq (act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ)))) ≤ C' := by
  first | exact @GlobalTheory.ClassFin.SiegelBound.borel_harishChandra | exact GlobalTheory.ClassFin.SiegelBound.borel_harishChandra | (intros; apply GlobalTheory.ClassFin.SiegelBound.borel_harishChandra <;> assumption)
