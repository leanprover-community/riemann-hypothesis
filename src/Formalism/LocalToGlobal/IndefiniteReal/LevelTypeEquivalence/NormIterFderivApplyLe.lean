import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSym

namespace Formalism.IndefR.Eqv

open scoped ContDiff
open Filter Topology

section MD

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def md (φ : V → ℂ) : (n : ℕ) → (Fin n → V) → ℝ → V → ℂ
  | 0, _, _, a => φ a
  | n + 1, v, h, a => (md φ n (Fin.tail v) h (a + h • v 0) - md φ n (Fin.tail v) h a) / h


end MD

section MD2

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]



theorem contDiff_fderiv_apply {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) (w : V) : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y w) :=
  (ContinuousLinearMap.apply ℝ ℂ w).contDiff.comp (hφ.fderiv_right (m := ∞) (by simp))


end MD2

section MD3

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]




end MD3

end Formalism.IndefR.Eqv
