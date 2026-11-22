module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace Formalism.L2.G.Triv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev SV (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

section Trace

end Trace

section Lattice

variable {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] [NumberField F] [Algebra F E] in
theorem den_upper (Λ : Submodule (𝓞 E) (n → E)) [Finite n] (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
  classical
  have := Fintype.ofFinite n
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  refine ⟨m, hm0, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
  | zero => intro k; simp [isIntegral_zero]
  | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
  | smul r x _ hx =>
    intro k
    have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
      simp [Algebra.smul_def]; ring
    rw [this]
    exact (RingOfIntegers.isIntegral_coe r).mul (hx k)

omit [NumberField F] [Algebra F E] in
theorem den_lower (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ := by
  classical
  have hk : ∀ k : n, ∃ N : ℕ, ∃ f : Fin N → E, ∃ w : Fin N → Λ,
      ∑ j, f j • (w j : n → E) = Pi.single k 1 := by
    intro k
    have : (Pi.single k 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨N, f, w, h⟩ := Submodule.mem_span_set'.1 this
    exact ⟨N, f, fun j => ⟨w j, (w j).2⟩, h⟩
  choose N f w hw using hk
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : Σ k : n, Fin (N k) => f p.1 p.2)
  refine ⟨m, hm0, fun k => ?_⟩
  have : (Pi.single k (m : E) : n → E) =
      ∑ j, (⟨(m : E) * f k j, hm ⟨k, j⟩⟩ : 𝓞 E) • (w k j : n → E) := by
    have h1 : (Pi.single k (m : E) : n → E) = (m : E) • (Pi.single k 1 : n → E) := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    rw [h1, ← hw k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul E, smul_smul]
    rfl
  rw [this]
  exact sum_mem fun j _ => Λ.smul_mem _ (w k j).2

theorem incl_int (v : HeightOneSpectrum (𝓞 F)) (e : E) (he : IsIntegral ℤ e) :
    inclE (F := F) (v.adicCompletion F) e ∈ SV E v := by
  apply Subring.subset_closure
  left
  exact ⟨⟨e, ⟨⟨e, he⟩, rfl⟩⟩, rfl⟩

theorem loc_upper (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ) (hm : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k))
    (v : HeightOneSpectrum (𝓞 F)) (y : n → E ⊗[F] v.adicCompletion F)
    (hy : y ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ) (i : n) :
    inclE (F := F) (v.adicCompletion F) (m : E) * y i ∈ SV E v := by
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨x, hx, rfl⟩ := hy'
    rw [← map_mul]
    exact incl_int v _ (hm x hx i)
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, mul_add]
    exact add_mem ha hb
  | smul s a _ ha =>
    simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
    rw [mul_left_comm]
    exact mul_mem s.2 ha

theorem loc_lower (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ) (hm : ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ)
    (v : HeightOneSpectrum (𝓞 F)) (y : n → E ⊗[F] v.adicCompletion F) (hy : ∀ i, y i ∈ SV E v) :
    (fun i => inclE (F := F) (v.adicCompletion F) (m : E) * y i) ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ := by
  have key : (fun i => inclE (F := F) (v.adicCompletion F) (m : E) * y i) =
      ∑ k, (⟨y k, hy k⟩ : SV E v) • (fun i => inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : n → E) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show _ = y i * inclE (F := F) (v.adicCompletion F) ((Pi.single i (m : E) : n → E) i)
      rw [Pi.single_eq_same, mul_comm]
    · intro k _ hk
      show y k * inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : n → E) i) = 0
      rw [Pi.single_eq_of_ne (Ne.symm hk), map_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [key]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hm k, rfl⟩)

def latLoc (F : Type) [Field F] [NumberField F] [Algebra F E] (Λ : Submodule (𝓞 E) (n → E)) :
    Submodule (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F),
    (fun i => prV (E := E) v (x i)) ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ}
  add_mem' := by
    intro a b ha hb v
    have : (fun i => prV (E := E) v ((a + b) i)) = (fun i => prV (E := E) v (a i)) + fun i => prV (E := E) v (b i) := by
      ext i; simp
    rw [this]; exact add_mem (ha v) (hb v)
  zero_mem' := by
    intro v
    have : (fun i => prV (E := E) v ((0 : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  smul_mem' := by
    intro s a ha v
    have : (fun i => prV (E := E) v ((s • a) i)) =
        (⟨prV (E := E) v s, afsplit_prV_int v _ s.2⟩ : SV E v) • fun i => prV (E := E) v (a i) := by
      ext i
      show prV (E := E) v ((s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * a i) = prV (E := E) v s * prV (E := E) v (a i)
      rw [map_mul]
    rw [this]; exact Submodule.smul_mem _ _ (ha v)

end Lattice

end Formalism.L2.G.Triv

end
