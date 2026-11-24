module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
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

open UpperTheory.V UpperTheory.V.Af.Fin in
private theorem lie_eq_lam {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (i j : Fin a) (x : Cinf E)
    (φ : Sm E a) :
    Cm.smEq E a (lie E a (toL (Matrix.single i j x)) φ) =
      lam E a (Matrix.single i j (Cm.mixEq E x)) (Cm.smEq E a φ) := by
  rw [← Cm.uAction_ι_smEq, lam_apply]
  congr 3
  refine Subtype.ext (Matrix.ext fun k l => ?_)
  change Cm.mixEq E (Matrix.single i j x k l) = Matrix.single i j (Cm.mixEq E x) k l
  simp only [Matrix.single_apply, apply_ite (Cm.mixEq E), map_zero]

open UpperTheory.V UpperTheory.V.Af.Fin in
theorem UpperTheory.V.Cj.S.slice :
    UpperTheory.V.Cj.S.Slice := by
  intro E _ _ _ a n e g
  obtain ⟨f, hf, hl⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie E a n e g
  have key : ∀ i j x ψ, (Cm.smEq E a).symm (f (Cm.smEq E n (lie E n (toL (Matrix.single (e i) (e j) x)) ψ))) =
      lie E a (toL (Matrix.single i j x)) ((Cm.smEq E a).symm (f (Cm.smEq E n ψ))) := fun i j x ψ => by
    rw [LinearEquiv.symm_apply_eq, lie_eq_lam, lie_eq_lam, LinearEquiv.apply_symm_apply, ← matrixExtendByZero_single, hl]
  refine ⟨(Cm.smEq E a).symm.toLinearMap ∘ₗ f ∘ₗ (Cm.smEq E n).toLinearMap, fun ψ x => hf _ x, fun t i j ψ => ?_⟩
  rw [← Cm.uC_genC, ← Cm.uC_genC]
  simp only [Cm.genC, AlgRepEndIrreducible.eL, map_smul, map_sub, Cm.uC_ιC, LinearMap.smul_apply, LinearMap.sub_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, key]
