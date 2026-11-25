module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalProduct

@[expose] public section

noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount.OrbKProd

open GlobalTheory.BCT GlobalTheory.BCT.OrbProd

theorem finsum_prod_mul {α β : Type} (u : α → ℂ) (v : β → ℂ) :
    ∑ᶠ z : α × β, u z.1 * v z.2 = (∑ᶠ a, u a) * ∑ᶠ b, v b := by
  apply _root_.GlobalTheory.BCT.StTwTens.finsum_prod_mul' <;> assumption

section Vol

variable {G : Type} [Group G]

theorem vol_eq_idxRatio (C H : Subgroup G) : vol C H = GlobalTheory.FunObj.idxRatio H C := rfl

theorem vol_prod {G' : Type} [Group G'] (C H : Subgroup G) (C' H' : Subgroup G') :
    vol (C.prod C') (H.prod H') = vol C H * vol C' H' := by
  unfold vol
  rw [relIndex_prod_prod, relIndex_prod_prod]
  push_cast
  exact mul_div_mul_comm _ _ _ _

theorem inf_map_conj (T A : Subgroup G) {t : G} (ht : t ∈ T) :
    T ⊓ A.map (MulAut.conj t).toMonoidHom = (T ⊓ A).map (MulAut.conj t).toMonoidHom := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective, map_conj_self _ ht]

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Vol

section Term

variable {G : Type} [Group G]

def oTerm (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) (x : G) : ℂ :=
  ((vol C (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom) : ℚ) : ℂ)⁻¹ * f (x⁻¹ * δ * θ x)

theorem orbC_eq (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) :
    orbC θ K C δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G), oTerm θ K C δ f (Quotient.out q) :=
  rfl

theorem f_inv (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (hf : ∀ k ∈ K, ∀ y, f (k⁻¹ * y * θ k) = f y)
    {t k : G} (ht : t ∈ twCent θ δ) (hk : k ∈ K) (x : G) :
    f ((t * x * k)⁻¹ * δ * θ (t * x * k)) = f (x⁻¹ * δ * θ x) := by
  have ht0 : t * δ = δ * θ t := ht
  have ht' : θ t = δ⁻¹ * (t * δ) := eq_inv_mul_of_mul_eq ht0.symm
  rw [← hf k hk (x⁻¹ * δ * θ x)]
  congr 1
  simp only [map_mul, _root_.mul_inv_rev, ht']
  group

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Term

end GlobalTheory.LKCount.OrbKProd
