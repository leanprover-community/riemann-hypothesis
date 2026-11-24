module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocyclePullbackRepresentation
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

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

theorem _root_.GlobalTheory.T.exists_cocycle_pullbackRepresentation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → (∀ f ∈ M.cusp ka, IsInv M f) → ∃ a : U → C → ℂˣ, (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) ∧ ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom), ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
  first | exact @GlobalTheory.PullCocycle.exists_cocycle | exact GlobalTheory.PullCocycle.exists_cocycle | (intros; apply GlobalTheory.PullCocycle.exists_cocycle <;> assumption)
