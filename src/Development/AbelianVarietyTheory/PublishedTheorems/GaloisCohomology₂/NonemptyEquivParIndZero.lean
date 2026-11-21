import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsSumMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivProdIrrZero

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocGL.ProjLine Matrix

namespace GlobalTheory.Published.LanglandsSumTests

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {χ : kˣ →* ℂˣ}




theorem eq_of_isLSeg_single {ρ x : IrrGL k} (hρ : ρ.IsCusp) (h : IsLSeg (.single ρ hρ) x.rep) : x = ρ := by
  obtain ⟨n, c⟩ := x
  obtain ⟨d, c'⟩ := ρ
  obtain rfl : d = n := (one_mul d).symm.trans h.deg_eq
  exact congrArg _ (irrCl_eq_iff.2 ((single_spec hρ).2.1.unique h))

theorem factors_eq (hχ : IsSmoothChar χ) {h : ℕ} {x : Fin h → IrrGL k}
    (H : LFactors ({Segment.single _ (IrrGL.isCusp_ofChar χ hχ)} +
      {Segment.single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)}) x) :
    h = 2 ∧ HEq x ![(IrrGL.ofChar χ hχ).nu 1, IrrGL.ofChar χ hχ] := by
  obtain ⟨Δ, ⟨hm, ho⟩, hΔ⟩ := H
  obtain rfl : h = 2 := by simpa using congrArg Multiset.card hm
  have hm' : ({Δ 0, Δ 1} : Multiset (Segment k)) =
    {.single _ (IrrGL.isCusp_ofChar χ hχ), .single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)} := hm
  have hp := single_precedes χ hχ
  have h01 : Δ 0 = .single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1) ∧ Δ 1 = .single _ (IrrGL.isCusp_ofChar χ hχ) := by
    rcases Multiset.cons_eq_cons.1 hm' with ⟨a, b⟩ | ⟨-, s, a, b⟩
    · exact absurd hp.1 (by rw [← a, ← Multiset.singleton_inj.1 b]; exact ho 0 1 (by decide))
    · obtain rfl : s = 0 := by simpa using congrArg Multiset.card a
      exact ⟨(Multiset.singleton_inj.1 b).symm, Multiset.singleton_inj.1 a⟩
  refine ⟨rfl, heq_of_eq (funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩))⟩
  · exact eq_of_isLSeg_single _ (h01.1 ▸ hΔ 0)
  · exact eq_of_isLSeg_single _ (h01.2 ▸ hΔ 1)

theorem equiv_of_isL (hχ : IsSmoothChar χ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin 2) k) V} (H : IsL ({Segment.single _ (IrrGL.isCusp_ofChar χ hχ)} +
      {Segment.single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)}) π) :
    Nonempty (π.Equiv (detRep (Fin 2) (χ * absPow k (1 / 2)))) := by
  obtain ⟨_, x, hd, hx, hc⟩ := H
  obtain ⟨_, y, hd', hy, hc'⟩ := isL_detRep_two hχ
  obtain ⟨rfl, h1⟩ := factors_eq hχ hx
  obtain ⟨rfl, h2⟩ := factors_eq hχ hy
  obtain rfl : x = y := eq_of_heq (h1.trans h2.symm)
  exact hc'.unique hc


example : IsNonarchimedeanLocalField ℚ_[2] ∧ CharZero ℚ_[2] ∧ IsSmoothChar (1 : ℚ_[2]ˣ →* ℂˣ) :=
  ⟨inferInstance, inferInstance, isSmoothChar_one⟩

theorem nonempty_equiv_parInd_zero {α V : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [AddCommGroup V] [Module ℂ V] (e : (Σ a, m a) ≃ Fin 0)
    (ρ : Representation ℂ (Levi k m) V) (L : ℂ ≃ₗ[ℂ] V) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (parInd e ρ)) := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp e ρ :=
    { toFun := fun c => ⟨⟨fun _ => L c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_add L a b))
      map_smul' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_smul L a b)) }
  refine ⟨equivOfBijective ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ ⟨fun a b h => ?_, fun φ => ?_⟩⟩
  · have h1 : L a = L b := congrArg (fun φ : IndSp e ρ => φ.1.1 1) h
    exact L.injective h1
  · refine ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    rw [hg g]
    exact L.apply_symm_apply _



end GlobalTheory.Published.LanglandsSumTests

end
