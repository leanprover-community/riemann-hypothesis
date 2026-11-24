module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.WeightAlgebra

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.abelian₂

open NumberField Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.L2.LamCM

variable {D : D7}

theorem mean_restrict {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (f : (K →+* ℂ) → ℝ) :
    (∑ σ : L →+* ℂ, f (σ.comp (algebraMap K L))) / (Module.finrank ℚ L : ℝ) =
      (∑ τ : K →+* ℂ, f τ) / (Module.finrank ℚ K : ℝ) := by
  classical
  have hfib : ∀ τ : K →+* ℂ, (Finset.univ.filter fun σ : L →+* ℂ => σ.comp (algebraMap K L) = τ).card =
      Module.finrank K L := by
    intro τ
    let _ : Algebra K ℂ := τ.toAlgebra
    let e : {σ : L →+* ℂ // σ.comp (algebraMap K L) = τ} ≃ (L →ₐ[K] ℂ) :=
      { toFun := fun σ => ⟨σ.1, fun a => congrFun (congrArg DFunLike.coe σ.2) a⟩
        invFun := fun φ => ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩
        left_inv := fun σ => rfl
        right_inv := fun φ => rfl }
    rw [← Fintype.card_subtype, Fintype.card_congr e, AlgHom.card]
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : L →+* ℂ => σ.comp (algebraMap K L))
    (fun σ => f (σ.comp (algebraMap K L)))]
  have h1 : ∀ τ : K →+* ℂ, (∑ σ ∈ Finset.univ.filter fun σ : L →+* ℂ => σ.comp (algebraMap K L) = τ,
      f (σ.comp (algebraMap K L))) = (Module.finrank K L : ℝ) * f τ := by
    intro τ
    rw [Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2], Finset.sum_const, hfib τ,
      nsmul_eq_mul]
  simp only [h1, ← Finset.mul_sum]
  rw [← Module.finrank_mul_finrank ℚ K L]
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hKL : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  push_cast
  field_simp

end Formalism.L2.Pj.abelian₂
