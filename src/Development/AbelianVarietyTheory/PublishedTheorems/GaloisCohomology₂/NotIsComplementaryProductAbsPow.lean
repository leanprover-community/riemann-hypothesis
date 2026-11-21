import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.GenericUnitary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem IsUnitaryLSeg.deg_pos {x : IrrGL k} (h : IsUnitaryLSeg x) : 0 < x.1 := by
  obtain ⟨⟨Δ, hΔ⟩, -⟩ := h
  rw [← hΔ.deg_eq]
  exact Nat.mul_pos Δ.len_pos Δ.d_pos



omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem isCuspidal_of_isSmooth_one {π : Representation ℂ (GL (Fin 1) k) V} (hs : IsSmooth π) : IsCuspidal π := by
  refine ⟨hs, fun s d e he => absurd ?_ he⟩
  rw [eq_bot_iff]
  intro u hu
  have := det_eq_one_of_mem_unipRad k hu
  rw [Subgroup.mem_bot]
  ext i j
  have h := congrArg Units.val this
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simpa using h


theorem nonempty_equiv_prodIrr_zero (x : Fin 0 → IrrGL k) (hd : ∑ a, (x a).1 = 0) :
    Nonempty ((Representation.trivial ℂ (GL (Fin 0) k) ℂ).Equiv (prodIrr x hd)) := by
  let L := (PiTensorProduct.isEmptyEquiv (R := ℂ) (Fin 0) (s := fun a => (x a).2.rep.V)).symm
  have h1 : ∀ g : GL (Fin 0) k, g = 1 := fun g => Subsingleton.elim _ _
  let f : (Representation.trivial ℂ (GL (Fin 0) k) ℂ).IntertwiningMap (prodIrr x hd) :=
    { toFun := fun v => ⟨⟨fun _ => L v, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (h1 _)
          simp⟩, mem_smoothPart_of_nhds (Filter.univ_mem' fun g => by rw [h1 g]; simp)⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun _ => L.map_smul c v))
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun _ => rfl)) }
  refine ⟨equivOfBijective f ⟨fun v w h => ?_, fun φ => ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩⟩⟩
  · exact L.injective (congrArg (fun φ => φ.1.1 1) h)
  · rw [h1 g]; exact L.apply_symm_apply _


end GlobalTheory.GenericUnitary
