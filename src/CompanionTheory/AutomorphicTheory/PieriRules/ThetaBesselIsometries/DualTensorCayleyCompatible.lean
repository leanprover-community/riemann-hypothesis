module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyCompatible
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.StatementKT
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DualTensorCapelliIntertwineStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.RawTens

def lm {k r : ℕ} {R R' : Rep k r} {T : R.H → R'.H} (h : SmMap R R' T) : R.smSub →ₗ[ℂ] R'.smSub where
  toFun v := ⟨T v, h.mem v v.2⟩
  map_add' v w := Subtype.ext (h.add v v.2 w w.2)
  map_smul' a v := Subtype.ext (h.smul a v v.2)

@[simp] theorem lm_coe {k r : ℕ} {R R' : Rep k r} {T : R.H → R'.H} (h : SmMap R R' T) (v : R.smSub) :
    ((lm h v : R'.smSub) : R'.H) = T v := rfl

section alg

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem change_inv (A B : Matrix (Fin n) (Fin n) ℂ) (h : A * B = 1) (x : Fin n → M) (c : Fin n) :
    ∑ d, B d c • ∑ e, A e d • x e = x c :=
  _root_.GlobalTheory.RawTens.change_inv A B h x c

theorem dualTens_sum {ι : Type} (S : Finset ι) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n)
    (x : ι → Fin n → M) : dualTens E a b (∑ i ∈ S, x i) = ∑ i ∈ S, dualTens E a b (x i) :=
  _root_.GlobalTheory.RawTens.dualTens_sum S E a b x

theorem alg {N : Fin n → Type} [∀ s, AddCommGroup (N s)] [∀ s, Module ℂ (N s)]
    (I : ∀ s, Fin n → N s →ₗ[ℂ] M) (P : ∀ s, Fin n → M →ₗ[ℂ] N s)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (hBA : B * A = 1)
    (E : Fin n → Fin n → Module.End ℂ M) (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s))
    (hI : ∀ s a b y c, I s c (F s a b y) =
      E a b (I s c y) - ∑ j, (B * Matrix.single a b (1 : ℂ) * A) j c • I s j y)
    (h1 : ∀ (x : Fin n → M) c, ∑ s, I s c (∑ d, P s d (x d)) = x c)
    (h2 : ∀ s y, ∑ c, P s c (I s c y) = y)
    (h3 : ∀ s t, s ≠ t → ∀ y, ∑ c, P s c (I t c y) = 0) :
    ∃ (io' : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr' : ∀ s, (Fin n → M) →ₗ[ℂ] N s),
      (∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y)) ∧
      (∀ s a b x, pr' s (dualTens E a b x) = F s a b (pr' s x)) ∧
      (∀ x, ∑ s, io' s (pr' s x) = x) ∧ (∀ s y, pr' s (io' s y) = y) ∧
      (∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0) ∧
      (∀ s y d, io' s y d = ∑ c, B c d • I s c y) ∧
      ∀ s x, pr' s x = ∑ c, P s c (∑ d, A d c • x d) :=
  _root_.GlobalTheory.RawTens.alg I P A B hAB hBA E F hI h1 h2 h3

end alg

theorem rawTens : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDG ε (muI s)) → TensRaw dualM R RI io pr → IsUnit Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), (∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y)) ∧ (∀ s a b x, pr' s (dualTens E a b x) = F s a b (pr' s x)) ∧ (∀ x, ∑ s, io' s (pr' s x) = x) ∧ (∀ s y, pr' s (io' s y) = y) ∧ (∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0) ∧ (∀ s y d, ((io' s y d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • io s c (y : (RI s).H)) ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) :=
  fun h1 k r ε mu R h2 RI muI io pr Q E F h3 =>
    _root_.GlobalTheory.RawTens.rawTens h1 k r ε mu R (GlobalTheory.isDS_of_isDG h2) RI muI io pr Q E F (fun s => GlobalTheory.isDS_of_isDG (h3 s))

end GlobalTheory.RawTens
