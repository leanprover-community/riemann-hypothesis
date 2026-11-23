module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcResidue
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalLinearForms

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]
  {k : Type} [Field k] {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')}
  {α : T → k} {M : T → Fin i → k}

theorem span_alpha (h : IsExcResidueData b b' α M) : Submodule.span ℤ (Set.range α) = ⊤ := by
  obtain ⟨-, ρ', -, -, hρ', -, -, -, -, hα, -⟩ := h
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨φ, rfl⟩ := hρ' x

  rw [← b'.sum_repr φ, map_sum]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [map_zsmul, ← hα t]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

theorem linFormsIndep (h : IsExcResidueData b b' α M) : LinFormsIndep M := by
  obtain ⟨-, -, σ, -, -, hσ, -, -, -, -, hM⟩ := h
  intro w hw
  funext j
  obtain ⟨φ, hφ⟩ := hσ (Pi.single j 1)
  have hcomb : ∀ j', σ φ j' = ∑ t, (b.repr φ t : k) * M t j' := by
    intro j'
    have hs : σ φ = ∑ t, b.repr φ t • M t := by
      conv_lhs => rw [← b.sum_repr φ]

      rw [map_sum]
      simp_rw [map_zsmul, hM]
    rw [hs, Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
  have key : ∑ j', σ φ j' * w j' = 0 := by
    simp only [hcomb, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum, hw t, mul_zero]
  rw [hφ] at key
  simpa [Pi.single_apply] using key

end StackedExceptionalLinearForms


open StackedExceptionalLinearForms in
theorem DualStackedExcLinear.proof (hEx : DualStackedExcResidueExists.Statement)
    (hBase : DualStackedExcBaseLe.Statement) (hLe : DualStackedExcLinPrimeLe.Statement) :
    DualStackedExcLinear.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab E hE
  obtain ⟨k, hk, hkf, α, M, hD, hcard⟩ := hEx K i F F' T b b' a hi hlt hcov hab
  have h1 : stackedBase b' a ≤ linPrime α M := hBase K i F F' T b b' a hi hlt hcov hab k α M hD
  have h2 : linPrime α M ≤ E := hLe K i F F' T b b' a hi hlt hcov hab k α M hD E hE.1.1.1 hE.1.1.2 hE.2
  have hprime : (linPrime α M).IsPrime := RingHom.ker_isPrime _
  exact ⟨k, hk, hkf, α, M, span_alpha hD, linFormsIndep hD, le_antisymm (hE.1.2 ⟨hprime, h1⟩ h2) h2, hcard⟩

end

end GroundTheory.Heights₂.Heights
