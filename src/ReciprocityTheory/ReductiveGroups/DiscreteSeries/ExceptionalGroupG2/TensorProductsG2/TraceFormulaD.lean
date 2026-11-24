module

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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaD

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem tensor_functor_separation (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d)
    {y : H} (hy : y ∈ closGen E V) {ζ ζ' : Fin n → H} (hζ : ∀ c, ζ c ∈ closGen E V)
    (hζ' : ∀ c, ζ' c ∈ closGen E V)
    (hm : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hm' : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ' (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    inner ℂ (tfPh dual ε σ y ζ) (tfJ ε (tfPh dual ε σ y ζ')) = tfFormBH ε ζ ζ' * inner ℂ y y / (d : ℂ) := by
  set F : (Fin n → H) → Fin n → Formalism.REAL.UJ ε → ℂ := fun ζ c g =>
    coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ (Formalism.MainNotions.S.umat g) with hF
  have h1 : ∀ c, inner ℂ (tfPh dual ε σ y ζ c) (tfJ ε (tfPh dual ε σ y ζ') c) =
      ∫ g, tfSgn ε c * (star (F ζ c g) * F ζ' c g) ∂(Formalism.REAL.muG ε) := fun c => by
    rw [tfJ_apply, inner_smul_right, integral_const_mul, tfPh_apply, tfPh_apply, L2.inner_def]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [coe_toL2_ae_eq_of_memLp (hm c), coe_toL2_ae_eq_of_memLp (hm' c)] with g e1 e2
    rw [e1, e2, RCLike.inner_apply, mul_comm]
    rfl
  have hi : ∀ c, Integrable (fun g => tfSgn ε c * (star (F ζ c g) * F ζ' c g)) (Formalism.REAL.muG ε) :=
    fun c => ((hm c).star.integrable_mul (hm' c)).const_mul _
  have hs := fun c => tfClRep_schur hgap hσ hD hV hc hVK hd hy (hζ' c) hy (hζ c)
  rw [PiLp.inner_apply, sum_congr rfl fun c _ => h1 c, ← integral_finsetSum _ fun c _ => hi c]
  have h2 : ∀ g : Formalism.REAL.UJ ε, ∑ c, tfSgn ε c * (star (F ζ c g) * F ζ' c g) =
      ∑ c, tfSgn ε c * (inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ' c)) *
        star (inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ c)))) := fun g => by
    have h3 := tf_jquad (tfCoef dual (Formalism.MainNotions.S.umat g)) (tfSgn ε) (tfCoef_orth dual (umat_mem_UJset ε g))
      (fun c => inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ c))) (fun c => inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ' c)))
    refine Eq.trans (sum_congr rfl fun c _ => ?_) (h3.trans (sum_congr rfl fun c _ => by ring))
    simp only [hF, tfd_coef, star_mul', tf_star_sgn]
    linear_combination (tfSgn ε c * star (∑ d, tfCoef dual (Formalism.MainNotions.S.umat g) c d *
      inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ d))) * ∑ d, tfCoef dual (Formalism.MainNotions.S.umat g) c d *
        inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ' d))) * tfSgn_mul_self ε c
  simp only [h2]
  rw [integral_finsetSum _ fun c _ => (hs c).1.const_mul _, tfFormBH, sum_mul, sum_div]
  refine sum_congr rfl fun c _ => ?_
  rw [integral_const_mul, (hs c).2]
  ring

end ReciprocityTheory.ChartRestriction.DS.G2
