import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CstSApply

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.FrobCong

theorem sigma_eq_pow_add (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a) :
    ∃ x : Wq l a, sigma l a w = w ^ l + (l : Wq l a) * x := by
  have h0 : sigma l a w - w ^ l ∈ Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow]
    simp [WittVector.constantCoeff_apply, coeff_sigma]
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 h0
  exact ⟨x, by rw [mul_comm, hx]; ring⟩

end GlobalTheory.FrobCong
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittTiltFrobenius_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a), ∃ x : Wq l a, sigma l a w = w ^ l + (l : Wq l a) * x := by
  atlas_forward_decl GlobalTheory.FrobCong.sigma_eq_pow_add
