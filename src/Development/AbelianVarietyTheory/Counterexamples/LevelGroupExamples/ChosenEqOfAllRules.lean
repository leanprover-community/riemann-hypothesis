import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt

noncomputable section

namespace GlobalTheory.SupNormExample

open Formalism.L2.Pj

variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)

def conjAt (σ : K →+* ℂ) : CAt σ →ₐ[K] CAt ((starRingEnd ℂ).comp σ) :=
  { (starRingEnd ℂ : ℂ →+* ℂ) with commutes' := fun _ => rfl }

theorem ptNorm_conj (σ : K →+* ℂ) (fn : pts (CAt σ) → ι → ℝ)
    (fn' : pts (CAt ((starRingEnd ℂ).comp σ)) → ι → ℝ) (e : ι → ℕ) (f : Rules pts)
    (y : pts (CAt σ)) (z : pts (CAt ((starRingEnd ℂ).comp σ)))
    (hv : evalAt pts mapR f z = conjAt σ (evalAt pts mapR f y)) (hn : ∀ i, |fn' z i| = |fn y i|) :
    ptNorm pts mapR _ fn' e f z = ptNorm pts mapR σ fn e f y := by
  unfold ptNorm
  rw [hv]
  simp only [hn]
  congr 1
  exact RCLike.norm_conj (K := ℂ) _



end GlobalTheory.SupNormExample
