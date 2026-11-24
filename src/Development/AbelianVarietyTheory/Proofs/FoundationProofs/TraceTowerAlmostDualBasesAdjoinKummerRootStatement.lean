module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceTowerAlmostDualBasesAdjoinKummerRoot
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

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.traceTower_almostDualBases_adjoin_kummer_root : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ (ι : Type) [Fintype ι] (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) → (∀ k, v k ∈ FixI (Hfix T r)) →
  ∑ k, u k * v k = (p : Ω) → (∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0) →
  ∃ tr : Ω → Ω, DualData (FixI (Hinf T)) (FixI (Hfix T r)) u v tr := by
  first | exact @GlobalTheory.traceTower_dualData | exact GlobalTheory.traceTower_dualData | (intros; apply GlobalTheory.traceTower_dualData <;> assumption)
