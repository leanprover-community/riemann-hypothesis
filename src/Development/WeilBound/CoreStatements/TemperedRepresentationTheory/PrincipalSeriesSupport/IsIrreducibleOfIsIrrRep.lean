import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationUnitsMapEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtTensorTwistApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffTendsto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.MultiIrr GlobalTheory.LocGL.SupportRing

namespace Ysupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_hasSupport (hS : SubEmbedding) (x : IrrGL k) : ∃ s, HasSupport x.rep s := by
  obtain ⟨c, y, hd, hc, φ, hφ⟩ := hS k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr
  exact ⟨_, hasSupport_of_isSubquotient x.2.rep.irr hc (.of_injective φ hφ)⟩

theorem hasSupport_of_isSubquotient_prodIrr (hP : ProdSupport) {c N : ℕ} {y : Fin c → IrrGL k}
    {hd : ∑ a, (y a).1 = N} {t : Fin c → Multiset (IrrGL k)} (ht : ∀ a, HasSupport (y a).rep (t a))
    {π : Representation ℂ (GL (Fin N) k) V} (hi : π.IsIrreducible) (h : IsSubquotient π (prodIrr y hd)) :
    HasSupport π (∑ a, t a) :=
  hP k c N y hd t ht V π hi h

end Ysupp
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace Ysupp.UnramifiedTwistSupport

open GlobalTheory

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LocGL
open scoped TensorProduct

variable {g : ℕ} [Fact g.Prime]

theorem isUnram_of_supp {ν : ℚ_[g]ˣ →* ℂˣ} (h : Supp.IsUnram ν) : GlobalTheory.SplitWeil.IsUnram ν := by
  intro x hx
  have a1 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g (x : ℚ_[g]) 1
  have a2 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 (x : ℚ_[g])
  rw [hx, map_one] at a1 a2
  have h1 : ‖(x : ℚ_[g])‖ = 1 := by
    simp only [lt_self_iff_false, norm_one, false_iff, not_lt] at a1 a2
    exact le_antisymm a2 a1
  have := h (PadicInt.mkUnits h1)
  convert this using 2
  exact Units.ext rfl

theorem extTensor_twist_apply {a b : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (χ₁ : GL (Fin a) ℚ_[g] →* ℂˣ) (χ₂ : GL (Fin b) ℚ_[g] →* ℂˣ) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g])
    (w : W ⊗[ℂ] W') :
    extTensor (twist σ χ₁) (twist ρ χ₂) (x, y) w = ((χ₁ x * χ₂ y : ℂˣ) : ℂ) • TensorProduct.map (σ x) (ρ y) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, hu, hv, map_add, smul_add]
  | tmul u v =>
    rw [extTensor_tmul, TensorProduct.map_tmul, twist_apply, twist_apply, TensorProduct.smul_tmul_smul,
      Units.val_mul]

theorem scal_eq (ν₁ ν₂ A B : ℚ_[g]ˣ →* ℂˣ) (u v : ℚ_[g]ˣ) :
    (A u * B v) * ((ν₁ * A⁻¹) u * (ν₂ * B⁻¹) v) = ν₁ u * ν₂ v := by
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem law {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W ⊗[ℂ] W')
    (hΛ : ∀ (p : GL (Fin (a + b)) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
      (∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0) →
      (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j) →
      (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j)) →
      ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
        TensorProduct.map (σ x) (ρ y) (Λ v))
    (q : parab ℚ_[g] (two (stdSum (rfl : a + b = a + b)))) (w : V) :
    Λ (π q w) = (deltaHalf ℚ_[g] (Two (Fin a) (Fin b)) (leviProj ℚ_[g] _ q) : ℂ) •
      extTensor (twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)))
        (twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)))
        ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)) (Λ w) := by
  set X := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).1 with hX
  set Y := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).2 with hY
  have hL : leviProj ℚ_[g] _ q = leviTwo ℚ_[g] _ _ (X, Y) := (MulEquiv.apply_symm_apply _ _).symm
  have hpar := (mem_parab_two ℚ_[g]).1 q.2
  have h0 : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) →
      ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0 := by
    intro i j hj hi
    have e1 : stdSum (rfl : a + b = a + b) (.inr ⟨i - a, by omega⟩) = i := Fin.ext (by rw [stdSum_inr]; simp; omega)
    have e2 : stdSum (rfl : a + b = a + b) (.inl ⟨j, hj⟩) = j := Fin.ext (by rw [stdSum_inl])
    have := hpar ⟨i - a, by omega⟩ ⟨j, hj⟩
    rwa [e1, e2] at this
  have hx : ∀ i j : Fin a, (X : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j := by
    intro i j
    have hi := i.2
    have hj := j.2
    rw [Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos ⟨by omega, by omega⟩]
    show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inl i)) (stdSum (rfl : a + b = a + b) (.inl j)) = _
    congr 1 <;> exact Fin.ext (stdSum_inl _ _)
  have hy : ∀ i j : Fin b, (Y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j) := by
    intro i j
    have hi := i.2
    have hj := j.2
    rw [Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos ⟨by omega, by omega⟩]
    show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inr i)) (stdSum (rfl : a + b = a + b) (.inr j)) = _
    congr 1 <;> exact Fin.ext (stdSum_inr _ _)
  rw [hΛ q X Y h0 hx hy w, hL, MulEquiv.symm_apply_apply, deltaHalf_two, extTensor_twist_apply, smul_smul,
    ← Units.val_mul, detChar_apply, detChar_apply]
  simp only [Fintype.card_fin]
  rw [scal_eq]

theorem supp_of_mapsToProd : Ysupp.ProdSupport → ∀ (g : ℕ) [Fact g.Prime] (n a b : ℕ) (V W W' : Type)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W)
    (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W'),
    GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → Supp.MapsToProd π σ ρ →
    ∀ (ys yr : Multiset (GlobalTheory.LocGL.IrrGL ℚ_[g])), GlobalTheory.LocGL.HasSupport σ ys → GlobalTheory.LocGL.HasSupport ρ yr →
    ∃ (μ₁ μ₂ : ℚ_[g]ˣ →* ℂˣ) (h₁ : GlobalTheory.SplitWeil.IsUnram μ₁) (h₂ : GlobalTheory.SplitWeil.IsUnram μ₂),
      GlobalTheory.LocGL.HasSupport π (ys.map (fun x => x.tw μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₁)) +
        yr.map (fun x => x.tw μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₂))) := by
  intro hP g _ n a b V W W' _ _ _ _ _ _ π σ ρ hs hπ hM ys yr hys hyr
  obtain ⟨hn, ν₁, ν₂, Λ, h₁, h₂, hΛ0, hΛ⟩ := hM
  subst hn
  have hμ₁ : GlobalTheory.SplitWeil.IsUnram (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹) :=
    isUnram_mul (isUnram_of_supp h₁) (isUnram_inv (isUnram_absPow _ _))
  have hμ₂ : GlobalTheory.SplitWeil.IsUnram (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹) :=
    isUnram_mul (isUnram_of_supp h₂) (isUnram_inv (isUnram_absPow _ _))
  refine ⟨_, _, hμ₁, hμ₂, ?_⟩
  let T : π.IntertwiningMap (prod₂ (twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)))
      (twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)))) :=
    { toFun := fun v => ⟨⟨fun x => Λ (π x v), fun q x => by
          show Λ (π (q * x) v) = _
          rw [map_mul, Module.End.mul_apply]
          exact law π σ ρ ν₁ ν₂ Λ hΛ q (π x v)⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hs v).mem_nhds (by simp)) fun h hh => by
          have hh' : π h v = v := hh
          refine Subtype.ext (funext fun x => ?_)
          show Λ (π (x * h) v) = Λ (π x v)
          rw [map_mul, Module.End.mul_apply, hh'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (v + w)) = Λ (π x v) + Λ (π x w)
        rw [map_add, map_add]))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (c • v)) = c • Λ (π x v)
        rw [map_smul, map_smul]))
      isIntertwining' := fun h => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (π h v)) = Λ (π (x * h) v)
        rw [map_mul, Module.End.mul_apply])) }
  have hT : Function.Injective T := by
    haveI := hπ
    refine (Representation.IsIrreducible.injective_or_eq_zero T).resolve_right fun h0 => hΛ0 (LinearMap.ext fun v => ?_)
    have h1 : (T v).1.1 1 = 0 := by rw [h0]; rfl
    change Λ (π 1 v) = 0 at h1
    simpa using h1
  have hσ' := hys.tw _ (isSmoothChar_of_isUnram hμ₁)
  have hρ' := hyr.tw _ (isSmoothChar_of_isUnram hμ₂)
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr _ hσ'.isSmooth hσ'.isIrreducible _ hρ'.isSmooth hρ'.isIrreducible
    (Fin.sum_univ_two _)
  have hsub := (IsSubquotient.of_injective T hT).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have key := Ysupp.hasSupport_of_isSubquotient_prodIrr hP
    (t := ![_, _]) (Fin.forall_fin_two.2 ⟨hσ'.of_equiv (IrrGL.equivOf _ _ _), hρ'.of_equiv (IrrGL.equivOf _ _ _)⟩)
    hπ hsub
  rw [Fin.sum_univ_two] at key
  exact key

end Ysupp.UnramifiedTwistSupport
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace Ysupp.IrreducibleSupport

open GlobalTheory GlobalTheory.SerSys

section Chain

open GlobalTheory.LocGL

theorem isIrreducible_of_isIrrRep {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : IsIrrRep ρ) : ρ.IsIrreducible := by
  obtain ⟨hn, hW⟩ := h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => hv ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← e] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  · rcases hW S.toSubmodule (fun x w hw => S.apply_mem_toSubmodule x hw) with h0 | h1
    · exact Or.inl (Subrepresentation.ext (by rw [h0]; rfl))
    · exact Or.inr (Subrepresentation.ext (by rw [h1]; rfl))

theorem isIrrRep_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : IsIrrRep ρ := by
  haveI := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)
    exact bot_ne_top this
  · rcases eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

theorem hasSupport_zero (hS : Ysupp.SubEmbedding) {g : ℕ} [Fact g.Prime] {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin 0) ℚ_[g]) V) (hs : GlobalTheory.PRep.IsSmooth π)
    (hi : π.IsIrreducible) : HasSupport π (0 : Multiset (IrrGL ℚ_[g])) := by
  obtain ⟨s, hs'⟩ := Ysupp.exists_hasSupport hS (IrrGL.of π hs hi)
  have h1 : HasSupport π s := hs'.of_equiv (IrrGL.equivOf π hs hi).symm
  have h2 := h1.sum_fst
  rw [Fintype.card_fin] at h2
  have h3 : s = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hne
    have h4 := (h1.isCusp hy).1
    have h5 : y.1 ≤ (s.map Sigma.fst).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hy)
    omega
  rwa [h3] at h1

theorem chain : Ysupp.SubEmbedding → Ysupp.ProdSupport → ∀ (g : ℕ) [Fact g.Prime] (π : Supp.GLRep g), IsIrrRep π.2.ρ → GlobalTheory.PRep.IsSmooth π.2.ρ → ∃ (L : List (Supp.GLRep g)) (y : List (GlobalTheory.LocGL.IrrGL ℚ_[g])), Supp.InInd π L ∧ (∀ ρ ∈ L, 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ GlobalTheory.PRep.IsSmooth ρ.2.ρ ∧ ρ.2.ρ.IsIrreducible ∧ GlobalTheory.SmGL.IsCuspidal ρ.2.ρ) ∧ GlobalTheory.LocGL.HasSupport π.2.ρ (y : Multiset (GlobalTheory.LocGL.IrrGL ℚ_[g])) ∧ List.Forall₂ (fun (ρ : Supp.GLRep g) (x : GlobalTheory.LocGL.IrrGL ℚ_[g]) => ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (GlobalTheory.LocGL.IrrGL.of ρ.2.ρ hs hi).Inert x) L y := by
  intro hS hP g _
  have H : ∀ (N : ℕ) (π : Supp.GLRep g), π.1 = N → IsIrrRep π.2.ρ → GlobalTheory.PRep.IsSmooth π.2.ρ →
      ∃ (L : List (Supp.GLRep g)) (y : List (IrrGL ℚ_[g])), Supp.InInd π L ∧
        (∀ ρ ∈ L, 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ GlobalTheory.PRep.IsSmooth ρ.2.ρ ∧ ρ.2.ρ.IsIrreducible ∧
          GlobalTheory.SmGL.IsCuspidal ρ.2.ρ) ∧ HasSupport π.2.ρ (y : Multiset (IrrGL ℚ_[g])) ∧
        List.Forall₂ (fun (ρ : Supp.GLRep g) (x : IrrGL ℚ_[g]) =>
          ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (IrrGL.of ρ.2.ρ hs hi).Inert x) L y := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro π hN hπ hs
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · subst h0
        refine ⟨[], [], Supp.InInd.nil π hN hπ, by simp, ?_, List.Forall₂.nil⟩
        obtain ⟨n, π⟩ := π
        simp only at hN
        subst hN
        exact hasSupport_zero hS _ hs (isIrreducible_of_isIrrRep hπ)
      · obtain ⟨a, b, hab, W, W', _, _, _, _, σ, ρ, hb, hσs, hσi, hρs, hρi, hρc, φ, hφ⟩ :=
          GlobalTheory.JacFactor.exists_map_jac₂ ℚ_[g] π.1 _ π.2.ρ hs (isIrreducible_of_isIrrRep hπ) (hN ▸ hpos)
        have hM : Supp.MapsToProd π.2.ρ σ ρ := GlobalTheory.GLp.Supp.mapsToProd_of_jac₂ g a b π.1 hab _ _ _ π.2.ρ σ ρ φ hφ
        let σ' : Supp.GLRep g := ⟨a, Rep.of σ⟩
        let ρ' : Supp.GLRep g := ⟨b, Rep.of ρ⟩
        obtain ⟨Lσ, yσ, hI, hL, hS, hF⟩ :=
          ih a (by omega) σ' rfl (isIrrRep_of_isIrreducible hσi) hσs
        have hρsupp : HasSupport ρ {IrrGL.of ρ hρs hρi} :=
          (hasSupport_self (IrrGL.isCusp_of.2 ⟨hb, hρc⟩)).of_equiv (IrrGL.equivOf ρ hρs hρi).symm
        obtain ⟨μ₁, μ₂, h₁, h₂, hsupp⟩ := Ysupp.UnramifiedTwistSupport.supp_of_mapsToProd hP g _ _ _ _ _ _ π.2.ρ σ ρ hs (isIrreducible_of_isIrrRep hπ) hM
          yσ {IrrGL.of ρ hρs hρi} hS hρsupp
        refine ⟨ρ' :: Lσ, (IrrGL.of ρ hρs hρi).tw μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₂) ::
          yσ.map (fun x => x.tw μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₁)), ?_, ?_, ?_, ?_⟩
        · exact Supp.InInd.cons π σ' ρ' Lσ hπ (isIrrRep_of_isIrreducible hρi) hI hM
        · exact List.forall_mem_cons.2 ⟨⟨hb, isIrrRep_of_isIrreducible hρi, hρs, hρi, hρc⟩, hL⟩
        · convert hsupp using 1
          rw [← Multiset.cons_coe, ← Multiset.map_coe, Multiset.map_singleton, add_comm, Multiset.singleton_add]
        · refine List.Forall₂.cons ⟨hρs, hρi, μ₂, h₂, rfl⟩ ?_
          refine List.forall₂_map_right_iff.2 (hF.imp fun ρ x ⟨hs, hi, hin⟩ => ⟨hs, hi, ?_⟩)
          exact IrrGL.inert_equivalence.trans hin ⟨μ₁, h₁, rfl⟩
  intro π hπ hs
  exact H _ π rfl hπ hs

end Chain

end Ysupp.IrreducibleSupport
end
