import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem mem_fixed_iff' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ u ∈ K, ρ u v = v := by
  show (∀ h : K, ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, Subtype.forall]

theorem fixed_ne_bot_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (K : Subgroup G)
    (hf : fixed ρ K ≠ ⊥) : fixed σ K ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hf
  refine (Submodule.ne_bot_iff _).2 ⟨e v, mem_fixed_iff'.2 fun u hu => ?_, ?_⟩
  · have h1 : e (ρ u v) = σ u (e v) := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' u) v
    rw [mem_fixed_iff'.1 hv u hu] at h1
    exact h1.symm
  · intro h0
    apply hv0
    have := congrArg e.symm h0
    rwa [Representation.Equiv.symm_apply_apply, map_zero] at this


theorem val_lt_one_iff (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← Valuation.vlt_one_iff, ← Valuation.vlt_one_iff]


end PositivityTheory.LocalParametersCuspidal.DZC

end
