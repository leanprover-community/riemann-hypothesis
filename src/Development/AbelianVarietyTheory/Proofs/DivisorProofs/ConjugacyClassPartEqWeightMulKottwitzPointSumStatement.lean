module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugacyClassPartEqWeightMulKottwitzPointSum
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.conjugacyClassPart_eq_weight_mul_kottwitzPointSum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y₀ : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re → FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z) → ∀ y₀ : grp G β, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {y₀}) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K'), ((Nat.card (MulAction.stabilizer (grp G β) (Quotient.out o) ⊓ Subgroup.centralizer {y₀} : Subgroup (grp G β)) : ℕ) : ℂ)⁻¹ * GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y₀ = if (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y₀ z) then wt (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * pointSum ((toAfF G β x t hx).comp (Subgroup.centralizer {y₀}).subtype) ((toP1 G β).comp (Subgroup.centralizer {y₀}).subtype) (MonoidHom.id (Gr G 1)) Kf K' (toAfF G β x t hx y₀) (toP1 G β y₀) f f' else 0 := by
  first | (exact @GlobalTheory.CxUnfoldGen.cls_eq_of_uniq) | (exact GlobalTheory.CxUnfoldGen.cls_eq_of_uniq) | (intros; apply GlobalTheory.CxUnfoldGen.cls_eq_of_uniq  <;> assumption)
