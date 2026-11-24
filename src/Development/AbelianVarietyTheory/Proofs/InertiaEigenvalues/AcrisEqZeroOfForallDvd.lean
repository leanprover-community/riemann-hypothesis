module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU
open GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

def InJ (w : Per.Ainf l) : Prop := ∃ c : Per.OC l, Per.θ l w = (l : Per.OC l) * c

def IsLogJ (w : Per.Ainf l) (y : Per.Acris l) : Prop :=
  ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ s : Per.Acris0 l,
    ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) w) ^ (k + 1) ∧
    ∃ z : Per.Acris l, y - algebraMap (Per.Acris0 l) (Per.Acris l) s = ((l : ℕ) : Per.Acris l) ^ r * z

theorem isLogJ_zero : IsLogJ (0 : Per.Ainf l) 0 := fun _ => ⟨0, fun _ _ => ⟨0, by simp, 0, by simp⟩⟩

private theorem acris_eq_zero_of_forall_dvd (x : Per.Acris l)
    (h : ∀ r : ℕ, ∃ z : Per.Acris l, x = ((l : ℕ) : Per.Acris l) ^ r * z) : x = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {((l : ℕ) : Per.Acris l)})
    (GlobalTheory.MemLoc.acris_basic l).1.toIsHausdorff x fun r => ?_
  obtain ⟨z, hz⟩ := h r
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  exact ⟨z, hz⟩

theorem isLogJ_unique {w : Per.Ainf l} {y y' : Per.Acris l} (h : IsLogJ w y) (h' : IsLogJ w y') :
    y = y' := by
  rw [← sub_eq_zero]
  refine acris_eq_zero_of_forall_dvd (y - y') fun r => ?_
  obtain ⟨N, hN⟩ := h r
  obtain ⟨N', hN'⟩ := h' r
  obtain ⟨s, hs, z, hz⟩ := hN (max N N') (le_max_left _ _)
  obtain ⟨s', hs', z', hz'⟩ := hN' (max N N') (le_max_right _ _)
  have : s = s' := Subtype.ext
    ((GlobalTheory.RingBasics.isUnit_nat l _ (Nat.factorial_ne_zero _)).mul_left_cancel (hs.trans hs'.symm))
  subst this
  have key : y - y' = ((l : ℕ) : Per.Acris l) ^ r * (z - z') := by linear_combination hz - hz'
  exact ⟨z - z', key⟩

theorem isLogJ_extends {f : Per.Ainf l →+* Per.Ainf l} {F : Per.Acris l →+* Per.Acris l}
    (hf : GlobalTheory.CrisMaps.Extends f F) {w : Per.Ainf l} {y : Per.Acris l}
    (hy : IsLogJ w y) : IsLogJ (f w) (F y) := by
  intro r
  obtain ⟨N, hN⟩ := hy r
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨s, hs, z, hz⟩ := hN n hn
  refine ⟨⟨Per.extP f s, hf.mem _ s.2⟩, ?_, F z, ?_⟩
  · have := congrArg (Per.extP f) hs

    simpa only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one, GlobalTheory.RingBasics.awayMap_algebraMap₂] using this
  · have := congrArg F hz
    rw [map_sub, map_mul, map_pow, map_natCast, hf.env] at this
    exact this

theorem inJ_mu {e : Per.Fl l} (he : e.untilt = 1) : InJ (mu e) :=
  ⟨0, by rw [Model.theta_mu, he, sub_self, mul_zero]⟩

theorem inJ_pow {e : Per.Fl l} (h : InJ (Per.tm e - 1)) (m : ℕ) : InJ (Per.tm (e ^ m) - 1) := by
  obtain ⟨c, hc⟩ := h
  have hθ : Per.θ l (Per.tm e) - 1 = (l : Per.OC l) * c := by rw [← hc, map_sub, map_one]
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (Per.θ l (Per.tm e)) 1 m
  refine ⟨c * d, ?_⟩
  have e1 : Per.tm (e ^ m) = Per.tm e ^ m := map_pow (WittVector.teichmuller l) e m
  rw [e1, map_sub, map_one, map_pow, ← one_pow m, hd, hθ, mul_assoc]

end GlobalTheory.LogU
