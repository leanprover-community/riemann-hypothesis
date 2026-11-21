import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanSubMemSq
import BuildAid.ForwardExisting

section
open GlobalTheory
open scoped Pointwise

namespace GlobalTheory.NakAug

theorem surj : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (q : O), q ∈ IsLocalRing.maximalIdeal O → ∀ (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A), (∀ i, ε (x i) = 0) → (∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N) → Submodule.span O (Set.range fun i => AugCot.d ε (x i)) = ⊤ → Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O →ₐ[O] A) := by
  first
  | exact @_root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective
  | exact _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective
  | (apply _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective ..)

end GlobalTheory.NakAug
end

open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_surjective_of_cotangent_span_top : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (q : O), q ∈ IsLocalRing.maximalIdeal O → ∀ (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A), (∀ i, ε (x i) = 0) → (∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N) → Submodule.span O (Set.range fun i => AugCot.d ε (x i)) = ⊤ → Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O →ₐ[O] A) := by
  atlas_forward_decl GlobalTheory.NakAug.surj
