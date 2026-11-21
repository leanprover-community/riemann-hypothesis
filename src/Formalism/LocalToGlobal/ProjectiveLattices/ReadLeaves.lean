import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Formalism.LocalToGlobal.ProjectiveLattices.ChiProofs

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Test

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem wtC_of (hB : BorChartF Xo c) (hA : AllTest Xo c) (σ : c.F →+* ℂ) : WtC Xo c σ := by
  intro a n _ f hf t y y' hb
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  exact wtField_of_borChart hB a n f hf (CAt σ) t y y' (hA _ y) (hA _ y') hb


end Test

section Inv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}


end Inv

section Cont

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def DictLoc (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) : Prop :=
  ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : Comp) (x : GA D V → Frame (X k).Ψ r), ContinuousOn x N ∧
    ∀ g ∈ N, x g ∈ (X k).dom ∧ ∃ γ ∈ (X k).Γ, dict g = ⟨k, lact γ (x g)⟩

theorem adelCont_of {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} (hχ : ∀ k la γ, (X k).χ la γ = 1) (hL : DictLoc V dict) (hm : Continuous mu) :
    AdelCont V dict mu := by
  intro la P hP
  have h1 : ∀ k, P k ∈ (X k).SS (la k) := hP
  simp only [Data.SS, Set.mem_setOf_eq] at h1
  have hS : ∀ k, (X k).IsSec (la k) (P k) := fun k => (h1 k).1.1
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨N, hN, k, x, hx, hxN⟩ := hL g₀
  have hmap : Set.MapsTo x N (X k).dom := by
    intro g hg
    exact (hxN g hg).1
  have hcont : ContinuousOn (fun g => mu g * P k (x g)) N :=
    hm.continuousOn.mul ((hS k).1.continuousOn.comp hx hmap)
  have heq : ∀ g ∈ N, adel V dict mu P g = mu g * P k (x g) := by
    intro g hg
    obtain ⟨_, γ, hγ, hd⟩ := hxN g hg
    show mu g * P (dict g).1 (dict g).2 = _
    rw [hd]
    rw [(hS k).2.2 γ hγ (x g) (hxN g hg).1, hχ, one_mul]
  have hev : (fun g => mu g * P k (x g)) =ᶠ[nhds g₀] adel V dict mu P := by
    refine Filter.eventuallyEq_of_mem hN ?_
    intro g hg
    exact (heq g hg).symm
  exact (hcont.continuousAt hN).congr hev


end Cont

end Formalism.L2.Pj
