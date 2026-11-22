module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodOneGenus
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralHeckeForms

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable (D : D7)

variable {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (f : Fin D.R.rS → (VS D).V)

theorem vPr_perp (hf : PartnerOK D F0 f) (v : (VS D).V) : vPr D F0 f v ∈ perpS (VS D) F0.X := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    simp [vPr, hf.1]
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def vPrLin : (VS D).V →ₗ[D.host.E] (VS D).V where
  toFun := vPr D F0 f
  map_add' := vPr_add D F0 f
  map_smul' := vPr_smul D F0 f

def coordL (hf : PartnerOK D F0 f) :
    (VS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) × (WbQ D F0) × (Fin D.R.rS → D.host.E) :=
  LinearMap.prod (LinearMap.pi fun a => ((VS D).hT (f a)).comp (vPrLin D F0 f))
    (LinearMap.prod ((nX D F0).mkQ.comp (LinearMap.codRestrict _ (vPrLin D F0 f) (vPr_perp D F0 f hf)))
      (LinearMap.pi fun a => (VS D).hT (F0.e a)))

theorem coordL_apply (hf : PartnerOK D F0 f) (v : (VS D).V) :
    coordL D F0 f hf v = ((fun a => (VS D).hT (f a) (vPr D F0 f v)),
      (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) : WbQ D F0),
      (fun a => (VS D).hT (F0.e a) v)) := rfl

theorem coordL_injective (hf : PartnerOK D F0 f) : Function.Injective (coordL D F0 f hf) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [coordL_apply] at hv
  simp only [Prod.mk_eq_zero] at hv
  obtain ⟨h1, h2, h3⟩ := hv
  have hb : ∀ a, (VS D).hT (F0.e a) v = 0 := fun a => congrFun h3 a
  have hvv : vPr D F0 f v = v := by simp [vPr, hb]
  have hX : v ∈ F0.X := by
    rw [Submodule.Quotient.mk_eq_zero] at h2
    have : vPr D F0 f v ∈ F0.X := h2
    rwa [hvv] at this
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun D.host.E |>.1 hX
  have ha : ∀ a, (VS D).hT (f a) v = 0 := fun a => by
    have := congrFun h1 a
    rwa [hvv] at this
  have hc0 : ∀ a, c a = 0 := by
    intro a
    have h := ha a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum] at h
    have e : ∀ b, (VS D).hT (f a) (c b • F0.e b) = c b * (if b = a then 1 else 0) := by
      intro b
      rw [map_smul, smul_eq_mul, ← (VS D).herm.eq (F0.e b) (f a), hf.1 b a]
      split_ifs <;> simp
    simp only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  rw [← hc]
  simp [hc0]

theorem fi_bound (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    ∃ d : D.host.E, ∀ x ∈ I, ∃ o : 𝓞 D.host.E, x = (o : D.host.E) * d := by
  obtain ⟨d, hdS, hd⟩ := I.isFractional
  refine ⟨(algebraMap (𝓞 D.host.E) D.host.E d)⁻¹, fun x hx => ?_⟩
  obtain ⟨o, ho⟩ := hd x hx
  have hd0 : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact nonZeroDivisors.ne_zero hdS
  refine ⟨o, ?_⟩
  rw [Algebra.smul_def] at ho
  show x = algebraMap (𝓞 D.host.E) D.host.E o * _
  rw [ho]
  field_simp

theorem pi_mem_span {x : Fin D.R.rS → D.host.E} {d : Fin D.R.rS → D.host.E}
    (h : ∀ a, ∃ o : 𝓞 D.host.E, x a = (o : D.host.E) * d a) :
    x ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => (Pi.single a (d a) : Fin D.R.rS → D.host.E)) := by
  choose o ho using h
  have e : x = ∑ a, o a • (Pi.single a (d a) : Fin D.R.rS → D.host.E) := by
    ext b
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    simp [ho b]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem lamC_fg (hf : PartnerOK D F0 f) (M : Submodule (𝓞 D.host.E) (WbQ D F0)) (hM : M.FG) :
    (lamC D F0 f M).FG := by
  choose dα hdα using fun a => fi_bound D (aaI D a)
  choose dβ hdβ using fun a => fi_bound D (aaI D a)⁻¹
  let P : Submodule (𝓞 D.host.E) ((Fin D.R.rS → D.host.E) × (WbQ D F0) × (Fin D.R.rS → D.host.E)) :=
    (Submodule.span (𝓞 D.host.E) (Set.range fun a => (Pi.single a (dα a) : Fin D.R.rS → D.host.E))).prod
      (M.prod (Submodule.span (𝓞 D.host.E) (Set.range fun a =>
        (Pi.single a (star (dβ a)) : Fin D.R.rS → D.host.E))))
  have hPfg : P.FG := Submodule.FG.prod (Submodule.fg_span (Set.finite_range _))
    (Submodule.FG.prod hM (Submodule.fg_span (Set.finite_range _)))
  have hle : (lamC D F0 f M).map ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E)) ≤ P := by
    rintro _ ⟨v, ⟨h1, ⟨w, hw, hwM⟩, h3⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · exact pi_mem_span D (fun a => hdα a _ (h3 a))
    · have e : (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) = w := Subtype.ext hw.symm
      show (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) : WbQ D F0) ∈ M
      rw [e]; exact hwM
    · refine pi_mem_span D (fun a => ?_)
      obtain ⟨o, ho⟩ := hdβ a _ (h1 a)
      obtain ⟨o', ho'⟩ := star_int D o
      refine ⟨o', ?_⟩
      show (VS D).hT (F0.e a) v = _
      rw [ho', ← star_mul, mul_comm, ← ho, star_star]
  exact Submodule.fg_of_fg_map_injective ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E)) (coordL_injective D F0 f hf)
    (Submodule.FG.of_le (S := (lamC D F0 f M).map ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E))) hPfg hle)

theorem lattice_integral : LamLattice := by
  intro D u F0 f M hf hM
  exact Submodule.IsLattice.of_fg D.host.E (lamC_fg D F0 f hf M hM.1.fg)

end Lat

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
