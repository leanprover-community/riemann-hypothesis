import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def idTerm (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : B.DTerm k r Wp Wq where
  coef := fun _ => ContinuousLinearMap.id ℂ _
  coefAdj := fun _ => ContinuousLinearMap.id ℂ _
  word := []
  word_lie := by simp
  adj_id := by intros; rfl



theorem opOrder_le (D : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq) (h : C6.InDDPlus D fib L o κ Θ) :
    B.opOrder Θ ≤ o := by
  have hw : ∀ T ∈ Θ, T.word.length ≤ o := fun T hT => by
    obtain ⟨P, a, b, c, es, hP, hab, hlen, hlie, hco⟩ := h.2.2 T hT
    omega
  unfold B.opOrder
  clear h
  induction Θ with
  | nil => simp
  | cons T Θ ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (hw T (by simp)) (ih (fun T' hT' => hw T' (by simp [hT'])))




theorem inCC_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m m' : ℕ} (hm : m' ≤ m)
    {F : B.Mat k r → E} (hF : B.InCC A m F) : B.InCC A m' F := by
  obtain ⟨c, hck, hb⟩ := hF
  exact ⟨c, B5.ckOn_mono (by exact_mod_cast hm) hck, fun u v hu hv hl g hg => hb u v hu hv (le_trans hl hm) g hg⟩

theorem gf_cont (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous fun g : B.Mat k r => Gf k r z z' g := by
  obtain ⟨q, _, hq⟩ := P.gram_function_polynomial k r z z'
  have h1 : Continuous fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ) := by
    have e : (fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) =
        fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q := funext hq
    rw [e]
    refine (MvPolynomial.continuous_eval q).comp ?_
    refine continuous_pi fun i => ?_
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · simp only [Sum.elim_inl]; exact continuous_id.matrix_elem a b
    · simp only [Sum.elim_inr]; exact continuous_star.comp (continuous_id.matrix_elem a b)
  have := Complex.continuous_re.comp h1
  refine this.congr fun g => ?_
  simp



theorem cut_supp (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (χ₀ : ℝ → ℝ) (de : ℝ) (L : Finset (Fin (r + 2)))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) :
    ∀ g ∈ B.GV k r, C6.cutAll D χ₀ de L F g ≠ 0 → ε ≤ Gf k r D.z D.z' g := by
  intro g hg hne
  apply hF g hg
  intro h0
  apply hne
  simp [C6.cutAll, h0]

end ops

end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

namespace Formalism.FourierDecayAlt.P

open DifferentialOperatorClasses



end Formalism.FourierDecayAlt.P
