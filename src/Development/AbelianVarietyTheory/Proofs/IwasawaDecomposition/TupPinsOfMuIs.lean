module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTwistOfIsDelta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD.TupPin

theorem isTwist_types (B : Base) (f : Fr B.toPre) (T : TwDat B) :
    ∀ ξ ∈ T.set f, Chr.IsTwist B.host (Set.range B.host.g) ξ := by
  have a1 : Chr.IsTwist B.host (Set.range B.host.g) f.del := Chr.isTwist_of_isDelta B.host.pde_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde_prime B.pde_cond.1).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).1 h.symm) f.isDel
  have a2 : Chr.IsTwist B.host (Set.range B.host.g) f.del' := Chr.isTwist_of_isDelta B.host.pde'_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde'_prime B.pde_cond.2).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).2 h.symm) f.isDel'
  rintro ξ ((rfl | rfl | rfl) | ⟨w, rfl⟩)
  · exact Chr.isTwist_one _ _
  · exact a1
  · exact a2
  · have h := T.psi_tw w
    have a3 : Chr.IsTwist B.host (Set.range B.host.g) (T.psi w) := ⟨h.1, h.2.1, h.2.2.1, fun v hv =>
      ⟨(h.2.2.2 v hv).1, (h.2.2.2 v hv).2.1, (h.2.2.2 v hv).2.2.1,
        fun ⟨i, hi⟩ => (h.2.2.2 v hv).2.2.2 (Or.inr (Or.inl ⟨i, hi.symm⟩))⟩⟩
    unfold TwDat.xiTw
    split_ifs
    exacts [a2.mul_twist a3, a1.mul_twist a3]

theorem xiTw_unr (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : B.places.Pl) (v : HeightOneSpectrum (𝓞 B.host.E))
    (hv : OverP B.host (B.places.resChar w) v) : (T.xiTw f w).UnrAt v := by
  have hψ : (T.psi w).UnrAt v := fun x _ => (T.psi_is w).atl v hv x
  unfold TwDat.xiTw
  split_ifs with h
  · refine (f.isDel'.unr v fun hn => B.host.pde_ne ?_).mul hψ
    rw [h] at hv
    exact Examples₂.PlacesToy.prime_mem_unique v B.host.pde_prime B.host.pde'_prime hv hn
  · exact (f.isDel.unr v fun hn => h
      (Examples₂.PlacesToy.prime_mem_unique v (B.places.resChar_prime w) B.host.pde_prime hv hn)).mul hψ

end GlobalTheory.Mem.HD.TupPin
