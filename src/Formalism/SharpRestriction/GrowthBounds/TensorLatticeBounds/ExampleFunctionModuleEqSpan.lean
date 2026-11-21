import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataRank

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf} (C : Level P)

theorem mem_funMod (Hv : P.Tup → Submodule O P.Xsp) (F : P.Tup → P.Xsp) :
    F ∈ C.funMod Hv ↔ (∀ L, P.IsLatTup L → F L ∈ Hv L) ∧ (∀ L, ¬ P.IsLatTup L → F L = 0) ∧
      ∀ γ L, F (C.smul γ L) = ((C.χ γ : Oˣ) : O) • C.actX γ (F L) := by
  unfold Level.funMod
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.proj_apply,
    and_assoc, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply,
    sub_eq_zero]

end Gen

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def tup0 (h : HidaSetting p n' W Qq O Kf ι σ j w) : (places1 h).Tup := fun _ => line W p 0




def oneG (h : HidaSetting p n' W Qq O Kf ι σ j w) : (gat1 h).Fn := fun _ => oneFn (places1 h)








end Formalism.MainNotions.G.Inhab

end
