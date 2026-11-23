module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

theorem support_cxF_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → Set.Finite {y : grp G β | FixL G v β y z ∧ f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0}) → ∀ a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K', (Function.support (GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a)).Finite := by
  intro p _ G v wt Kf f _ K' f' _ β x t hx hfin a
  by_cases hpos : 0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
      (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re
  · refine (hfin (LeftCosets.rep _ _ a.1) _ hpos).subset ?_
    intro y hy
    rw [Function.mem_support] at hy
    unfold cxF at hy
    split_ifs at hy with hc
    · exact ⟨hc.2, left_ne_zero_of_mul hy⟩
    · exact absurd rfl hy
  · convert Set.finite_empty
    ext y
    simp only [Function.mem_support, Set.mem_empty_iff_false, iff_false, not_not]
    unfold cxF
    rw [if_neg (fun hc => hpos hc.1)]

end GlobalTheory.CxUnfold
