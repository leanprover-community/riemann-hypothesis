module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormForm
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormFormEmbeddings.proof (h : NormFormEval.Statement) : NormFormEmbeddings.Statement := by
  intro K L Ω _ _ _ _ _ _ _ _ _ n η
  have hs : ∀ _ : Fin n, (Set.range (algebraMap K Ω)).Infinite :=
    fun _ => Set.infinite_range_of_injective (algebraMap K Ω).injective
  refine MvPolynomial.funext_set (fun _ => Set.range (algebraMap K Ω)) hs ?_
  intro x hx
  choose u hu using fun m => hx m (Set.mem_univ m)
  obtain rfl : x = algebraMap K Ω ∘ u := funext fun m => (hu m).symm
  have hl : eval (algebraMap K Ω ∘ u) (map (algebraMap K Ω) (normForm K L η)) =
      algebraMap K Ω (eval u (normForm K L η)) := by
    rw [eval_map]
    change _ = algebraMap K Ω (eval₂ (RingHom.id K) u (normForm K L η))
    rw [eval₂_comp_left]
    rfl
  rw [hl, h K L n η u, Algebra.norm_eq_prod_embeddings]

  simp only [map_prod, map_sum, map_mul, eval_X, eval_C, Function.comp_apply]
  refine Finset.prod_congr rfl fun σ _ => Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, Algebra.smul_def]

end GroundTheory.Heights₂.Heights
