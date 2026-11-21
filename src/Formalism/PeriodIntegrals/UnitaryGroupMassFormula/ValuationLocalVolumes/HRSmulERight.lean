import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.InclRMemOEv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HostStarConj

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem sigR_alg (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, sigR_tmul_one]

theorem hR_smul_right (c : Fv F v) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c • hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_smul_left (c : Fv F v) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = c • hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, map_mul, sigR_alg]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_add_right (x y y' : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + y') = hR (Fv F v) σ J x y + hR (Fv F v) σ J x y' := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hR_add_left (x x' y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + x') y = hR (Fv F v) σ J x y + hR (Fv F v) σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hR_zero_right (x : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J x 0 = 0 := by
  simp [hR, Formalism.UG.hform]

theorem hR_zero_left (y : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J 0 y = 0 := by
  simp [hR, Formalism.UG.hform]

theorem oev_smul {c : v.adicCompletionIntegers F} {w : Fv F v ⊗[F] E} (hw : w ∈ OEv (E := E) v) :
    (c : Fv F v) • w ∈ OEv (E := E) v :=
  Submodule.smul_mem _ c hw

theorem hR_mem_of (Λ : Set (Fin n → E))
    (hL : ∀ a ∈ Λ, ∀ b ∈ Λ, ∃ o : 𝓞 E, hE σ J a b = (o : E))
    {x y : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v Λ) (hy : y ∈ latLoc (E := E) v Λ) :
    hR (Fv F v) σ J x y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      obtain ⟨o, ho⟩ := hL a ha b hb
      have h' : hR (Fv F v) σ J (fun i => inclR (Fv F v) (a i)) (fun i => inclR (Fv F v) (b i)) =
          inclR (Fv F v) (hE σ J a b) := hR_ratTup (Fv F v) σ J ![a, b] 0 1
      change hR (Fv F v) σ J (fun i => inclR (Fv F v) (a i)) (fun i => inclR (Fv F v) (b i)) ∈ _
      rw [h', ho]
      exact Submodule.subset_span ⟨o, trivial, rfl⟩
    | zero => rw [hR_zero_right]; exact Submodule.zero_mem _
    | add y y' _ _ h1 h2 => rw [hR_add_right]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h =>
      change hR (Fv F v) σ J _ ((c : Fv F v) • y) ∈ _
      rw [hR_smul_right]; exact oev_smul v h
  | zero => rw [hR_zero_left]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [hR_add_left]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    change hR (Fv F v) σ J ((c : Fv F v) • x) _ ∈ _
    rw [hR_smul_left]; exact oev_smul v h

end Gen

variable {D : D7} (X : HidaSetting D)

theorem hE_L (a : Fin X.B.I.n → X.B.I.E) (ha : a ∈ abelian₂ X) (b : Fin X.B.I.n → X.B.I.E) (hb : b ∈ abelian₂ X) :
    ∃ o : 𝓞 X.B.I.E, hE X.B.I.cm.sig X.B.I.J a b = (o : X.B.I.E) := by
  obtain ⟨o, ho⟩ := (X.B.I.L_dual b).1 hb a ha
  exact ⟨o, ho.symm⟩

theorem omVSD_fwd (v : PlX X) {x y : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E}
    (hx : x ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) (hy : y ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) :
    hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J x y ∈ OEv (E := X.B.I.E) v :=
  hR_mem_of X.B.I.cm.sig X.B.I.J v (abelian₂ X) (hE_L X) hx hy

def OmVSDBwd : Prop :=
  ∀ (v : PlX X) (y : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E),
    (∀ x ∈ latLoc (E := X.B.I.E) v (abelian₂ X), hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J x y ∈ OEv (E := X.B.I.E) v) →
      y ∈ latLoc (E := X.B.I.E) v (abelian₂ X)

theorem omVSD_of (h : OmVSDBwd X) : OmVSD X := fun v y =>
  ⟨fun hy x hx => omVSD_fwd X v hx hy, h v y⟩

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem hR_smulE_right (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_sum_right {ι : Type} (s : Finset ι) (x : Fin n → Fv F v ⊗[F] E) (f : ι → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (∑ i ∈ s, f i) = ∑ i ∈ s, hR (Fv F v) σ J x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hR_zero_right σ J v x
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hR_add_right, ih]

theorem oev_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, _, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, _, rfl⟩ := hy
      rw [← map_mul]
      exact Submodule.subset_span ⟨a * b, trivial, by simp⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y y' _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

end Gen

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem lat_oev_smul (v : PlX X) {c : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E} (hc : c ∈ OEv (E := X.B.I.E) v)
    {x : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E} (hx : x ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) :
    c • x ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨o, _, rfl⟩ := hc
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine Submodule.subset_span ⟨o • l, X.B.I.L.smul_mem o hl, ?_⟩
      funext i
      simp only [ratV, Pi.smul_apply, smul_eq_mul]
      rw [← map_mul]
      rfl
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
    | smul d x _ h =>
      beta_reduce
      beta_reduce at h
      have e : inclR (F := X.B.I.F) (Fv X.B.I.F v) (o : X.B.I.E) • (d • x) =
          d • (inclR (F := X.B.I.F) (Fv X.B.I.F v) (o : X.B.I.E) • x) := by
        funext i
        change _ * ((d : Fv X.B.I.F v) • x i) = (d : Fv X.B.I.F v) • (_ * x i)
        rw [mul_smul_comm]
      rw [e]; exact Submodule.smul_mem _ d h
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add c c' _ _ h1 h2 => rw [add_smul]; exact Submodule.add_mem _ h1 h2
  | smul d c _ h =>
    have e : (d • c) • x = d • (c • x) := by
      funext i
      change ((d : Fv X.B.I.F v) • c) * x i = (d : Fv X.B.I.F v) • (c * x i)
      rw [smul_mul_assoc]
    rw [e]; exact Submodule.smul_mem _ d h

abbrev zi : Fin (D.R.rS + 1 + D.R.rS) := Fin.castAdd D.R.rS (Fin.last D.R.rS)

theorem gramE_entry (j i : Fin (D.R.rS + 1 + D.R.rS)) :
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i = if i = piv D.R.rS j then cD X u' j else 0 := by
  rw [gram_eq, diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.Involutive.coe_toPerm]
  by_cases h : i = piv D.R.rS j
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (fun e => h e.symm), if_neg h, mul_zero]

def OmVMem : Prop := ∀ (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)), yTup X u' v i ∈ latLoc (E := X.B.I.E) v (abelian₂ X)

def OmVZPrim : Prop :=
  ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal → ∀ c : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E,
    c • yTup X u' v (zi (D := D)) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) → c ∈ OEv (E := X.B.I.E) v

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end
