module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Mathlib.Algebra.Module.StablyFree.Basic
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

noncomputable section

namespace GlobalTheory.KStableLie

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_of_isExp {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : IsExp L U)
    (N : Submodule ℂ V) (hL : ∀ y ∈ N, L y ∈ N) {v : V} (hv : v ∈ N) : U v ∈ N := by
  have hpow : ∀ m : ℕ, (L ^ m) v ∈ N := by
    intro m
    induction m with
    | zero => simpa using hv
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hL _ ih
  by_contra hn
  obtain ⟨l, hl, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hz : ∀ y ∈ N, l y = 0 := fun y hy => by
    have h' := Submodule.mem_map_of_mem (f := l) hy
    rw [hmap, Submodule.mem_bot] at h'
    exact h'
  have h0 : (fun m : ℕ => ((m.factorial : ℂ))⁻¹ * l ((L ^ m) v)) = fun _ => 0 := by
    funext m; rw [hz _ (hpow m), mul_zero]
  have hs := hU v l
  rw [h0] at hs
  exact hl (hs.unique hasSum_zero)


end GlobalTheory.KStableLie

end
