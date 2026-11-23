module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
import ReciprocityTheory.SemistableReduction.DetGramEqProdGramSchmidt

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem exists_basis_choice_det_ne_zero : ∀ (F E A A' : Type) [Field F] [Field E] [Algebra F E] [AddCommGroup A] [Module F A] [AddCommGroup A'] [Module E A'] (ι : A →ₛₗ[algebraMap F E] A') (V : Submodule F A) (r δ : ℕ) (bb : Module.Basis (Fin r) F V) (res : A' →ₗ[E] (Fin δ → E)), (Submodule.span E (ι '' (V : Set A))).map res = ⊤ → ∃ σ : Fin δ → Fin r, (Matrix.of fun p' p => res (ι (bb (σ p))) p').det ≠ 0 := by
  intro F E A A' _ _ _ _ _ _ _ ι V r δ bb res h
  have hsub : ι '' (V : Set A) ⊆ Submodule.span E (Set.range fun i => ι (bb i)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x = ∑ i, bb.repr ⟨x, hx⟩ i • ((bb i : V) : A) := by
      have := congrArg Subtype.val (bb.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm

    rw [hx', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span E (Set.range fun i => res (ι (bb i))) = ⊤ := by
    have h1 := Submodule.map_mono (f := res) (Submodule.span_le.mpr hsub)
    rw [h, Submodule.map_span, ← Set.range_comp] at h1
    exact eq_top_iff.mpr h1
  obtain ⟨b, hb, hbspan, hli⟩ := exists_linearIndependent E (Set.range fun i => res (ι (bb i)))
  let bs := Module.Basis.mk hli (by rw [Subtype.range_coe, hbspan, hspan])
  let e := bs.indexEquiv (Pi.basisFun E (Fin δ))
  have hmem : ∀ p, ((e.symm p : b) : Fin δ → E) ∈ Set.range fun i => res (ι (bb i)) :=
    fun p => hb (e.symm p).2
  choose σ hσ using hmem
  refine ⟨σ, ?_⟩
  have hli2 : LinearIndependent E (fun p => res (ι (bb (σ p)))) := by
    have : (fun p => res (ι (bb (σ p)))) = ((↑) : b → Fin δ → E) ∘ e.symm := funext fun p => hσ p
    rw [this]
    exact hli.comp _ e.symm.injective
  have hunit : IsUnit (Matrix.of fun p' p => res (ι (bb (σ p))) p') := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli2
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

end GlobalTheory
