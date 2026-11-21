import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactLatticeGL

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions

namespace GlobalTheory.UnitaryBC.Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

example (γ : latticeGL E n) (g : GA E n) : γ • g = γ.1 * g := rfl

variable (E n) in

abbrev constU : Submodule ℂ (UA E n → ℂ) := Submodule.span ℂ {(fun _ => 1 : UA E n → ℂ)}

theorem sum_one (n : ℕ) : ∑ _i : Fin 1, n = n := by simp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
omit [IsCMField E] in

theorem equiv_triv (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((Representation.trivial ℂ (GL (Fin n) (w.adicCompletion E)) ℂ).Equiv
      (locProd (N := fun _ : Fin 1 => n) (sum_one n) w fun _ => SmIrr.triv _)) :=
  GlobalTheory.LocGL.nonempty_equiv_multiProd_one (SmIrr.triv _).smooth _
    (fun a i => Fin.ext (by rw [GlobalTheory.SmGL.stdBlocks_val]; simp [Subsingleton.elim a 0]))

section Triv

variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ H W}

theorem act_eq (e : (Representation.trivial ℂ H ℂ).Equiv ρ) (g : H) (v : W) : ρ g v = v := by
  obtain ⟨c, rfl⟩ := e.toLinearEquiv.surjective v
  exact (LinearMap.congr_fun (e.isIntertwining' g) c).symm



end Triv



def zeroWt (n : ℕ) : DomWeight n := ⟨fun _ => 0, fun _ _ _ => le_rfl⟩



theorem coord_expU (τ : E →+* ℂ) (z : Cinf E) : coord τ (expU z).val = Complex.exp (coord τ z) := by
  unfold coord
  split_ifs
  · rfl
  · exact (Complex.exp_conj _).symm

theorem coord_atEmb_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) (z : ℂ) :
    coord τ' (atEmb τ z) = 0 := by
  classical
  unfold coord atEmb
  split_ifs <;> simp [Pi.single_eq_of_ne h]

def rot (τ : E →+* ℂ) (θ : ℝ) : UA E 1 :=
  ⟨infGL E 1 (CG.oneByOne (expU (atEmb τ (θ * Complex.I)))), by
    set g := infGL E 1 (CG.oneByOne (expU (atEmb τ (θ * Complex.I)))) with hg
    have h1 : pInf E (g.val 0 0) = (expU (atEmb τ (θ * Complex.I))).val :=
      congrArg (fun x : GL (Fin 1) (Cinf E) => x.val 0 0) (pInf_infGL (CG.oneByOne (expU (atEmb τ (θ * Complex.I)))))
    have h2 : pFin E (g.val 0 0) = 1 :=
      congrArg (fun x : GL (Fin 1) (Af E) => x.val 0 0) (pFin_infGL (CG.oneByOne (expU (atEmb τ (θ * Complex.I)))))
    have c1 : ∀ y, pInf E (conjAd E y) = star (pInf E y) := fun y => (infEq E).symm_apply_apply _
    have c2 : ∀ y, pFin E (conjAd E y) = conjFin (IsCMField.complexConj E).toRingEquiv (pFin E y) := fun y => rfl
    change cT (conjAd E) g.val * 1 * g.val = 1
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp only [Matrix.mul_one, Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.one_apply_eq]
    refine ad_ext ?_ ?_
    · rw [map_mul, c1, h1, map_one]
      funext w
      classical
      change starRingEnd ℂ (Complex.exp _) * Complex.exp _ = 1
      rw [← Complex.exp_conj, ← Complex.exp_add]
      by_cases h : w = InfinitePlace.mk τ
      · subst h
        unfold atEmb
        split_ifs <;> simp
      · simp [atEmb, Pi.single_eq_of_ne h]
    · rw [map_mul, c2, h2]; simp⟩

theorem cEmb_rot (τ τ' : E →+* ℂ) (θ : ℝ) :
    (cEmb τ' (rot τ θ)).val 0 0 = Complex.exp (coord τ' (atEmb τ (θ * Complex.I))) := by
  rw [← coord_expU]
  exact congrArg (coord τ') (congrArg (fun x : GL (Fin 1) (Cinf E) => x.val 0 0)
    (pInf_infGL (CG.oneByOne (expU (atEmb τ (θ * Complex.I))))))

theorem rot_mem (τ : E →+* ℂ) (θ : ℝ) : rot τ θ ∈ embU 1 τ := by
  refine ⟨pFin_infGL _, Subgroup.mem_iInf.2 fun τ' => Subgroup.mem_iInf.2 fun h => ?_⟩
  rw [MonoidHom.mem_ker]
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, cEmb_rot, coord_atEmb_ne h]
  simp









end GlobalTheory.UnitaryBC.Model

end
