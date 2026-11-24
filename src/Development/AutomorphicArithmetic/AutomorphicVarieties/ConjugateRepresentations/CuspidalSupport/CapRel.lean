module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModOfInjectiveIntertwining
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem slice_cap (h : UpperTheory.V.Cj.S.Slice) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a n : ℕ}
    (e : Fin a ↪ Fin n) (g : GA E n) :
    ∃ f : Sm E n →ₗ[ℂ] Sm E a, (∀ ψ x, (f ψ).1 x = ψ.1 (g * emb e x)) ∧
      ∀ t u ψ, cap t u (f ψ) = f (capB e t u ψ) := by
  obtain ⟨f, hf, hE⟩ := h E a n e g
  exact ⟨f, hf, fun t u ψ => (UpperTheory.algMod_of_injective_intertwining _ _ a f _ _ (hE t) _ ψ).symm⟩

theorem UpperTheory.V.Cj.S.capRel :
    UpperTheory.V.Cj.S.Slice → UpperTheory.V.Cj.S.CapBlock → UpperTheory.V.Cj.S.CapRel := by
  intro hS hB E _ _ _ r s ψ hψ t u
  refine ⟨res (capB (e1 r s) t (u - (s : ℂ) / 2) ψ).1, fun y => ?_, fun x => ?_⟩
  · obtain ⟨f, hf, hc⟩ := slice_cap hS (e1 r s) (emb (e2 r s) y)
    have key : ∀ φ : Sm E (r + s), (f φ).1 = fun x => res φ.1 x y := fun φ => funext fun x => by
      rw [hf, res, blk, UpperTheory.V.Af.Fin.emb_comm]
    exact ⟨f ψ, key ψ, by rw [hc, key]⟩
  · obtain ⟨f, hf, hc⟩ := slice_cap hS (e2 r s) (emb (e1 r s) x)
    have key : ∀ φ : Sm E (r + s), (f φ).1 = res φ.1 x := fun φ => funext fun y => hf φ y
    refine ⟨f _, key _, ?_⟩
    rw [hc, key]
    exact funext fun y => (hB E r s ψ hψ t u x y).symm
