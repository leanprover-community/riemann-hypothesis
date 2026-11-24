module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRootExchangeParabolicAndFourierJacobiIffEntri
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

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

theorem _root_.GlobalTheory.T.mem_rootExchangeParabolic_and_fourierJacobi_iff_entries : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ R k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) s ≤ Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ (1 ≤ ρ → ρ < c → ∀ g : GL (n ⊕ Fin c) k, g ∈ RFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) := by
  first | exact @GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff | exact GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff | (intros; apply GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff <;> assumption)
