module

public import Mathlib.Data.Nat.Notation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.V.Sd.Wc

private theorem sep_of_sum {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ p : V →ₗ[ℂ] X, p x ≠ 0 ∧ ∀ g y, p (τ g y) = σ g (p y) := by
  obtain ⟨-, hirr⟩ := (isIrreducible_iff σ).1 hσ
  have key : ∀ (f : X →ₗ[ℂ] V), (∀ g v, f (σ g v) = τ g (f v)) → ∀ U : Submodule ℂ V, (∀ g, ∀ v ∈ U, τ g v ∈ U) →
      ¬ LinearMap.range f ≤ U → ∀ x, f x ∈ U → x = 0 := by
    intro f hf U hU hn x hx
    rcases hirr (U.comap f) (fun g v hv => by
      rw [Submodule.mem_comap, hf]; exact hU g _ hv) with e | e
    · have : x ∈ U.comap f := hx
      rwa [e, Submodule.mem_bot] at this
    · exact absurd (LinearMap.range_le_iff_comap.2 e) hn
  obtain ⟨M, ⟨hst, hxM⟩, hmax⟩ := zorn_le₀ {U : Submodule ℂ V | (∀ g, ∀ v ∈ U, τ g v ∈ U) ∧ x ∉ U}
    (fun c hc hch => by
      rcases c.eq_empty_or_nonempty with rfl | hne
      · exact ⟨⊥, ⟨fun g v hv => by simp_all, by simpa using hx⟩, by simp⟩
      refine ⟨sSup c, ⟨fun g v hv => ?_, fun hv' => ?_⟩, fun z hz => le_sSup hz⟩
      · obtain ⟨U, hU, hvU⟩ := (Submodule.mem_sSup_of_directed hne hch.directedOn).1 hv
        exact le_sSup hU ((hc hU).1 g v hvU)
      · obtain ⟨U, hU, hvU⟩ := (Submodule.mem_sSup_of_directed hne hch.directedOn).1 hv'
        exact (hc hU).2 hvU)
  have hsup : ∀ f : X →ₗ[ℂ] V, (∀ g v, f (σ g v) = τ g (f v)) →
      ∀ g, ∀ v ∈ M ⊔ LinearMap.range f, τ g v ∈ M ⊔ LinearMap.range f := fun f hf g v hv => by
    obtain ⟨a, ha, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _), ← hf]
    exact Submodule.add_mem_sup (hst g a ha) ⟨_, rfl⟩
  have hmem : ∀ f : X →ₗ[ℂ] V, (∀ g v, f (σ g v) = τ g (f v)) → ¬ LinearMap.range f ≤ M →
      x ∈ M ⊔ LinearMap.range f := fun f hf hn => by
    by_contra hc
    exact hn (le_sup_right.trans (hmax ⟨hsup f hf, hc⟩ le_sup_left))
  obtain ⟨⟨f, hf⟩, hn⟩ : ∃ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, ¬ LinearMap.range f.1 ≤ M := by
    by_contra hn
    push Not at hn
    have : (⊤ : Submodule ℂ V) ≤ M := h ▸ iSup_le hn
    exact hxM (this trivial)
  have htop : (⊤ : Submodule ℂ V) ≤ M ⊔ LinearMap.range f := by
    rw [← h]
    refine iSup_le fun f' => ?_
    by_contra hc
    obtain ⟨a, ha, _, ⟨y, rfl⟩, e⟩ := Submodule.mem_sup.1 (hmem f'.1 f'.2 fun hl => hc (hl.trans le_sup_left))
    have h2 : f'.1 y ∈ M ⊔ LinearMap.range f := by
      rw [eq_sub_of_add_eq' e]
      exact Submodule.sub_mem _ (hmem f hf hn) (Submodule.mem_sup_left ha)
    have h3 := key f'.1 f'.2 _ (hsup f hf) hc y h2
    subst h3
    exact hxM (by rw [← e]; simpa using ha)
  have hbij : Function.Bijective (M.mkQ ∘ₗ f) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => key f hf M hst hn y ((Submodule.Quotient.mk_eq_zero M).1 hy), fun q => ?_⟩
    obtain ⟨v, rfl⟩ := M.mkQ_surjective q
    obtain ⟨a, ha, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := v)))
    refine ⟨y, ?_⟩
    rw [map_add (f := _), show M.mkQ a = 0 from (Submodule.Quotient.mk_eq_zero M).2 ha, zero_add]
    rfl
  let e := LinearEquiv.ofBijective _ hbij
  have hp : ∀ a ∈ M, ∀ y, e.symm (M.mkQ (a + f y)) = y := fun a ha y => by
    rw [map_add (f := _), show M.mkQ a = 0 from (Submodule.Quotient.mk_eq_zero M).2 ha, zero_add, LinearEquiv.symm_apply_eq]
    rfl
  refine ⟨e.symm.toLinearMap ∘ₗ M.mkQ, fun h0 => hxM ?_, fun g v => ?_⟩
  · exact (Submodule.Quotient.mk_eq_zero M).1 ((map_eq_zero_iff e.symm e.symm.injective).1 h0)
  · obtain ⟨a, ha, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := v)))
    change e.symm (M.mkQ _) = σ g (e.symm (M.mkQ _))
    rw [hp a ha, map_add (τ g), ← hf, hp _ (hst g a ha)]

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

private theorem cpt_fin (π : TR.CuspSub F n) (k : TR.Kinf F n) (g : GL (Fin n) (Af F)) (y : π.V) :
    π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
  refine Subtype.ext ?_
  change (TR.rt F n (TR.infGL F n (Unitary.toUnits k)) * TR.rt F n (finGL F n g)) y.1 =
    (TR.rt F n (finGL F n g) * TR.rt F n (TR.infGL F n (Unitary.toUnits k))) y.1
  rw [← map_mul, ← map_mul, TR.infGL_comm]

end UpperTheory.V.Sd.Wc
