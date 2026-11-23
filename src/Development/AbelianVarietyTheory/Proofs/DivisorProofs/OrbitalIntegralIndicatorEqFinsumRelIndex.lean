module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.OrbIndUnit

theorem avg_const_fun {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hs : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := uniqueOfSubsingleton (1 : H ⧸ (⊤ : Subgroup H))
  rw [finsum_unique]
  simp

theorem twOrb_id_indicator (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G) :
    twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := by
  unfold twOrb
  apply finsum_congr
  intro q
  set Q : G := Quotient.out q with hQ
  have hfun : (fun k : K => (K : Set G).indicator 1 ((Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k)))
      = fun _ => (K : Set G).indicator (1 : G → ℂ) (Q⁻¹ * γ * Q) := by
    funext k
    have he : (Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k) = (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k := by
      simp only [MonoidHom.id_apply]; group
    rw [he]
    by_cases h : Q⁻¹ * γ * Q ∈ K
    · have h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem k.2) h) k.2
      simp [Set.indicator_apply, h, h']
    · have h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∉ K := by
        intro h'
        apply h
        have := K.mul_mem (K.mul_mem k.2 h') (K.inv_mem k.2)
        simpa [mul_assoc] using this
      simp [Set.indicator_apply, h, h']
  rw [hfun, avg_const_fun]
  by_cases h : Q⁻¹ * γ * Q ∈ K
  · simp [Set.indicator_apply, h]
  · simp [Set.indicator_apply, h]

end GlobalTheory.OrbIndUnit
