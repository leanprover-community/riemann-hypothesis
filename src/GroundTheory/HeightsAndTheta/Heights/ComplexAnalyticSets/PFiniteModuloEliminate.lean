module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteModuloGeneralEquation
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeierstrassDivisionAtPoint
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem FiniteModuloEliminate.proof (hG : FiniteModuloGeneralEquation.Statement)
    (hW : WeierstrassDivisionAtPoint.Statement) : FiniteModuloEliminate.Statement := by
  intro σ τ _ _ _ x k f L c hf hfin hpow
  obtain ⟨d, F, hF, hFan, hhF, hFev, hord⟩ := hG σ τ x k f L c hf hfin hpow
  obtain ⟨n, e, he, hgen⟩ := hfin

  set t : (σ → ℂ) → ℂ := fun z => L z c - L x c with ht_def
  have ht : AnalyticAt ℂ t x :=
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c).comp L).analyticAt x).sub analyticAt_const
  let ix : Fin (n * d) → Fin n × Fin d := fun p => finProdFinEquiv.symm p
  refine ⟨n * d, fun p z => t z ^ ((ix p).2 : ℕ) * e (ix p).1 z, fun p => (ht.pow _).mul (he _), ?_⟩
  intro g hg
  obtain ⟨b, h, hb, hh, hev⟩ := hgen g hg
  choose q a hq ha hdiv using fun m => hW τ (L x) c d F (b m) hFan (hb m) hord
  have hLt : Tendsto L (𝓝 x) (𝓝 (L x)) := L.continuous.tendsto x
  refine ⟨fun p y => a (ix p).1 (ix p).2 y, fun i z => h i z + ∑ m, q m (L z) * e m z * hF i z,
    fun p => by simpa using ha (ix p).1 (ix p).2, fun i => ?_, ?_⟩
  · refine (hh i).add (Finset.univ.analyticAt_fun_sum fun m _ => ?_)
    have hqL : AnalyticAt ℂ (fun z => q m (L z)) x := (hq m).comp (L.analyticAt x)
    exact (hqL.mul (he m)).mul (hhF i)
  · have hdivL : ∀ᶠ z in 𝓝 x, ∀ m, b m (L z) = q m (L z) * F (L z) +
        ∑ j : Fin d, a m j (zeroCoordinate c (L z)) * (L z c - L x c) ^ (j : ℕ) :=
      eventually_all.2 fun m => hLt.eventually (hdiv m)
    filter_upwards [hev, hdivL, hFev] with z hz hzd hzF
    rw [hz]
    simp only [hzd, hzF, ContinuousLinearMap.comp_apply]
    have hre : ∀ φ : Fin n × Fin d → ℂ, ∑ p : Fin (n * d), φ (ix p) = ∑ m, ∑ j, φ (m, j) := fun φ => by
      rw [← Fintype.sum_prod_type']
      exact finProdFinEquiv.symm.sum_comp φ
    rw [hre (fun mj => a mj.1 mj.2 (zeroCoordinate c (L z)) * (t z ^ (mj.2 : ℕ) * e mj.1 z))]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, ht_def]
    have h1 : ∑ m, (q m (L z) * ∑ i, hF i z * f i z) * e m z =
        ∑ i, ∑ m, q m (L z) * e m z * hF i z * f i z := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
    have h2 : ∀ m (j : Fin d), a m j (zeroCoordinate c (L z)) * (L z c - L x c) ^ (j : ℕ) * e m z =
        a m j (zeroCoordinate c (L z)) * ((L z c - L x c) ^ (j : ℕ) * e m z) := fun m j => by ring
    simp only [h2]
    rw [h1]
    ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
