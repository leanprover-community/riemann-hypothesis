module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.RoadU.TwistSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nu_nu_neg (x : IrrGL (k := k)) (s : ℂ) : (x.nu s).nu (-s) = x := by
  rw [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]

theorem nu_injective (s : ℂ) : Function.Injective fun x : IrrGL (k := k) => x.nu s := fun x y h => by
  have := congrArg (fun z : IrrGL (k := k) => z.nu (-s)) h
  simpa only [nu_nu_neg] using this

theorem chars_eq_map_nu {n : ℕ} (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j))
    (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ) (h : ∀ j, ξ' j = ξ j * absPow k s) :
    chars ξ' hξ' = (chars ξ hξ).map fun y => y.nu s := by
  unfold chars
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, IrrGL.nu, IrrGL.tw_ofChar]
  exact IrrGL.ofChar_inj.2 (h j)

theorem unlinked_map_nu (m : Multiset (IrrGL (k := k))) (s : ℂ) :
    Unlinked (m.map fun y => y.nu s) ↔ Unlinked m := by
  constructor
  · intro h y hy z hz e
    refine h (y.nu s) (Multiset.mem_map_of_mem _ hy) (z.nu s) (Multiset.mem_map_of_mem _ hz) ?_
    rw [e, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]
  · intro h y' hy' z' hz' e
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hy'
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hz'
    refine h y hy z hz (nu_injective s ?_)
    simp only
    rw [e, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]

theorem supp_nu_chars : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (n : ℕ) (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ), (∀ j, ξ' j = ξ j * absPow k s) → (HasSupport x.rep (chars ξ hξ) ↔ HasSupport (x.nu s).rep (chars ξ' hξ')) ∧ (Unlinked (chars ξ hξ) ↔ Unlinked (chars ξ' hξ')) := by
  intro k _ _ _ _ _ x n ξ ξ' hξ hξ' s h
  rw [chars_eq_map_nu ξ ξ' hξ hξ' s h, unlinked_map_nu]
  refine ⟨⟨fun H => SupportRing.hasSupport_nu H s, fun H => ?_⟩, Iff.rfl⟩
  have H' := SupportRing.hasSupport_nu H (-s)
  rw [nu_nu_neg, Multiset.map_map] at H'
  simpa only [Function.comp_def, nu_nu_neg, Multiset.map_id'] using H'

end GlobalTheory.RoadU.TwistSupp
