module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.DetNatAbsLeProdL1Norms
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.indexLe :
    ∀ (ι : Type) [Finite ι] (v : ι → (ι →₀ ℤ)) (b : ℕ), LinearIndependent ℤ v → (∀ i, l1 (v i) ≤ b) →
      CardLe ((ι →₀ ℤ) ⧸ Submodule.span ℤ (Set.range v)) (b ^ Nat.card ι) := by
  intro ι _ v b hv hb
  classical
  haveI := Fintype.ofFinite ι
  set N := Submodule.span ℤ (Set.range v)
  let bE : Module.Basis ι ℤ (ι →₀ ℤ) := Finsupp.basisSingleOne
  let bN : Module.Basis ι ℤ N := Module.Basis.span hv
  have hfin : Finite ((ι →₀ ℤ) ⧸ N) := by
    apply Submodule.finiteQuotientOfFreeOfRankEq
    rw [Module.finrank_eq_card_basis bN, Module.finrank_eq_card_basis bE]
  refine ⟨hfin, ?_⟩
  rw [← Submodule.natAbs_det_basis_change bE N bN]
  have hcoe : ((↑) ∘ bN : ι → (ι →₀ ℤ)) = v := by
    funext i
    exact congrArg Subtype.val (Module.Basis.span_apply hv i)
  rw [hcoe, Module.Basis.det_apply, ← Matrix.det_transpose]
  refine (det_natAbs_le_prod_l1_norms ι _).trans ?_
  have hrow : ∀ i, ∑ k, ((bE.toMatrix v).transpose i k).natAbs = l1 (v i) := by
    intro i
    simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply, bE, Finsupp.basisSingleOne_repr,
      LinearEquiv.refl_apply, l1]
    rw [Finsupp.sum_fintype]
    simp
  simp_rw [hrow]
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact Finset.prod_le_pow_card _ _ _ (fun i _ => hb i)
