module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermUnipotentLeftInvariant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UpperTriangularEqUnipotentMulLevi
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

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.iwa :
    UpperTheory.V.Cj.S.RtK → UpperTheory.V.Cj.S.Iwa := by
  intro hK E _ _ _ r s φ m B hφ ⟨g, hg⟩
  obtain ⟨b, hb, k, hk, rfl⟩ := GroundTheory.Automorphic.Reduction.exists_adelicBorel_mul_maxCompact (K := E) (n := r + s) g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (GroundTheory.Automorphic.Reduction.mem_adelicBorel.1 hb)
  refine ⟨_, hK E (r + s) φ m B hφ k hk, m₁, m₂, ?_⟩
  have hl : GroundTheory.Automorphic.AutomorphicForm.IsLeftInvariant φ.1 := hφ.aut.left
  rw [mul_assoc, UpperTheory.constantTerm_unipotent_left_invariant E (r + s) r φ.1 hl] at hg
  rw [← GroundTheory.Automorphic.AutomorphicForm.constantTerm_rightTranslate] at hg
  exact hg
