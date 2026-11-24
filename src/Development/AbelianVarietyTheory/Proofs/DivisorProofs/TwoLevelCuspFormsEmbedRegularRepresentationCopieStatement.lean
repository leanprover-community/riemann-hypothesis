module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsEmbedRegularRepresentationCopie
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

theorem _root_.GlobalTheory.T.twoLevelCuspForms_embed_regularRepresentation_copies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → ∀ ep c : ℝ, Ranks M ka (sOf M) ep c → ∀ H : Subgroup U, LevelHyp (sub M H) → ∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := by
  first | exact @GlobalTheory.CuspEmb.cusp_embReg | exact GlobalTheory.CuspEmb.cusp_embReg | (intros; apply GlobalTheory.CuspEmb.cusp_embReg <;> assumption)
