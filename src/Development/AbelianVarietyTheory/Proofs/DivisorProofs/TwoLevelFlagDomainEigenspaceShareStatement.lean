module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainEigenspaceShare
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.twoLevelFlagDomain_eigenspace_share : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → ∀ ep c : ℝ, Ranks M ka (sOf M) ep c → ∀ H : Subgroup U, LevelHyp (sub M H) → ∀ lam : H →* ℂˣ, finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (sOf M))) ≤ Nat.card H * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) ∧ (1 - ep) * finrank ℂ (M.cusp ka) ≤ (Nat.card H : ℝ) * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) := by
  first | exact @GlobalTheory.ShareEig.share_eig | exact GlobalTheory.ShareEig.share_eig | (intros; apply GlobalTheory.ShareEig.share_eig <;> assumption)
