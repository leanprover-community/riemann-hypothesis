module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
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

noncomputable section

namespace PositivityTheory.Rg.BcB.F.FX.Bo.IsoInverse

open GlobalTheory.PRep

variable {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem mem_fixed_iff (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ h : K, ρ (h : G) v = v := by
  show (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp

variable {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}

theorem symm_intertwines (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) :
    ∀ g w, L.symm (ρ' g w) = ρ g (L.symm w) := by
  intro g w
  apply L.injective
  rw [hL, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem map_fixed_le (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) (K : Subgroup G) :
    (fixed ρ K).map (L : V →ₗ[ℂ] V') ≤ fixed ρ' K := by
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, mem_fixed_iff] at hv
  rw [mem_fixed_iff]
  intro h
  simp only [LinearEquiv.coe_coe]
  rw [← hL, hv h]

theorem map_fixed_eq (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) (K : Subgroup G) :
    (fixed ρ K).map (L : V →ₗ[ℂ] V') = fixed ρ' K := by
  refine le_antisymm (map_fixed_le L hL K) ?_
  intro w hw
  have hm : (L.symm : V' →ₗ[ℂ] V) w ∈ (fixed ρ' K).map (L.symm : V' →ₗ[ℂ] V) := ⟨w, hw, rfl⟩
  refine ⟨L.symm w, map_fixed_le L.symm (symm_intertwines L hL) K hm, ?_⟩
  simp

def imap (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) : ρ.IntertwiningMap ρ' :=
  ⟨(L : V →ₗ[ℂ] V'), fun g => by ext v; exact hL g v⟩

theorem isSubquotient_of (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) :
    GlobalTheory.SmGL.IsSubquotient ρ' ρ :=
  GlobalTheory.SmGL.IsSubquotient.of_surjective (imap L hL) (fun w => ⟨L.symm w, L.apply_symm_apply w⟩)

end PositivityTheory.Rg.BcB.F.FX.Bo.IsoInverse

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open GlobalTheory.PRep IsoInverse

theorem IsoInv_holds : IsoInv := by
  intro G V V' _ _ _ _ _ ρ ρ' ⟨e⟩ K
  have hL : ∀ g v, e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) := fun g v =>
    Representation.IntertwiningMap.isIntertwining (f := e.toIntertwiningMap) (g := g) (v := v)
  have hL' := symm_intertwines e.toLinearEquiv hL
  let F := e.toLinearEquiv.ofSubmodules _ _ (map_fixed_eq e.toLinearEquiv hL K)
  refine ⟨fun W _ _ τ => ⟨fun h => h.trans (isSubquotient_of e.toLinearEquiv.symm hL'),
    fun h => h.trans (isSubquotient_of e.toLinearEquiv hL)⟩, F.finrank_eq,
    ⟨fun _ => F.finiteDimensional, fun _ => F.symm.finiteDimensional⟩⟩

end PositivityTheory.Rg.BcB.F.FX.Bo
