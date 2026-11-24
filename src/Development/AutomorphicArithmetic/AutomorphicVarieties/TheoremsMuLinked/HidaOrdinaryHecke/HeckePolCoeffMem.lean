module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.frobS :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ) (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] (I : Ideal (H.TK θ a K)) (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K I D ψ →
    ∀ (i : ℕ) (g : H.Gq) (N : ℕ), ∃ s ∈ Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)), D.lam i (MonoidAlgebra.single g 1) - s ∈ I ^ N := by
  intro L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ a K _ I D ψ hU i g N
  have hlc := hU.cont i N
  obtain ⟨x, ⟨w, hw, B, σ, hB, hσ, rfl⟩, hxU⟩ :=
    hAx.dense.exists_mem_open (hlc.isOpen_fiber _) ⟨g, Set.mem_singleton _⟩
  refine ⟨D.lam i (MonoidAlgebra.single (H.prj σ⁻¹) 1), ?_, ?_⟩
  · have hf := hU.frob ⟨w, hw⟩ B σ hB hσ
    set_option synthInstance.maxHeartbeats 400000 in
    generalize hR : Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)) = R
    have hgen : ∀ j, H.genW θ a K ⟨w, hw⟩ j ∈ R := by
      intro j
      subst hR
      unfold UpperTheory.V.Hi.HSet.genW
      split_ifs with h
      · exact Algebra.subset_adjoin ⟨(⟨w, hw⟩, _), rfl⟩
      · exact Subalgebra.one_mem _
    show (-1) ^ i * (D.chi _).coeff (n - i) ∈ R
    rw [hf]
    refine R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) _) ?_
    unfold UpperTheory.V.Hi.heckePol
    rw [Polynomial.finsetSum_coeff]
    refine R.sum_mem fun j _ => ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs
    · exact R.mul_mem (R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) _)
        (R.pow_mem (R.natCast_mem _) _)) (hgen j)
    · exact R.zero_mem
  · have h1 := Set.mem_singleton_iff.mp hxU
    exact Ideal.Quotient.eq.mp h1.symm
