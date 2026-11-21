import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SUnitsEulerDifference
import Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepClosed
import Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepDescent
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC

section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

theorem finDim_of_isLat {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] (M : Submodule O V) (h : Formalism.LatticeIndexTer.IsLat O K V M) :
    FiniteDimensional K V := by
  obtain ⟨S, hS⟩ := h.1
  refine ⟨⟨S, ?_⟩⟩
  rw [← h.2, ← hS, Submodule.span_span_of_tower]

theorem qlen_inf_ne_top (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] (M Θ : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M)
    (hΘ : Formalism.LatticeIndexTer.IsLat O K V Θ) (W : Submodule O V) :
    Formalism.LatticeIndexTer.qlen O V (M ⊓ W) (Θ ⊓ W) ≠ ⊤ := by
  have hfin := Formalism.LatticeIndexTer.latFinite O K V M Θ hM hΘ
  unfold Formalism.LatticeIndexTer.qlen at hfin ⊢
  let g : ↥(M ⊓ W) →ₗ[O] (↥M ⧸ Θ.comap M.subtype) :=
    (Θ.comap M.subtype).mkQ ∘ₗ Submodule.inclusion inf_le_left
  have hker : LinearMap.ker g = (Θ ⊓ W).comap (M ⊓ W).subtype := by
    ext ⟨y, hy⟩
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_inclusion, Submodule.mem_inf]
    exact ⟨fun h => ⟨h, hy.2⟩, fun h => h.1⟩
  have hle := Module.length_le_of_injective (g.ker.liftQ g le_rfl)
    (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))
  rw [hker] at hle
  exact ne_top_of_le_ne_top hfin hle

theorem length_comap_eq {O V W : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W]
    [Module O W] (f : W →ₗ[O] V) (hf : Function.Injective f) (A B : Submodule O V)
    (hA : A ≤ LinearMap.range f) :
    Module.length O (↥(A.comap f) ⧸ (B.comap f).comap (A.comap f).subtype) =
      Module.length O (↥A ⧸ B.comap A.subtype) := by
  let g0 : ↥(A.comap f) →ₗ[O] ↥A := f.restrict (fun x hx => hx)
  have hg : Function.Bijective g0 := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply hf
      exact congrArg Subtype.val hxy
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hA hy
      exact ⟨⟨x, hy⟩, rfl⟩
  let g : ↥(A.comap f) ≃ₗ[O] ↥A := LinearEquiv.ofBijective g0 hg
  refine (Submodule.Quotient.equiv _ _ g ?_).length_eq
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨⟨x, hx⟩, hxB, hxy⟩
    have : f x = y := congrArg Subtype.val hxy
    simpa [← this] using hxB
  · intro hyB
    obtain ⟨x, rfl⟩ := hA hy
    exact ⟨⟨x, hy⟩, hyB, rfl⟩

theorem qlen_eq_zero_of_le {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (A B : Submodule O V)
    (h : B ≤ A) : Formalism.LatticeIndexTer.qlen O V B A = 0 := by
  unfold Formalism.LatticeIndexTer.qlen
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  induction a using Submodule.Quotient.induction_on with
  | _ x =>
    induction b using Submodule.Quotient.induction_on with
    | _ y => exact (Submodule.Quotient.eq _).2 (h (x - y).2)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}


theorem qlen_eq_inW (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO))
    (N N' : Submodule (X.Ol la) (X.Vl la)) (V' : Submodule (X.Kl la) (X.Vl la))
    (hV' : V' ≤ WL X ka la) :
    Formalism.LatticeIndexTer.qlen (X.Ol la) ↥(WL X ka la)
              (inW X ka la N ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
              (inW X ka la N' ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la)) =
      X.qlen la (N ⊓ X.ofK la V') (N' ⊓ X.ofK la V') := by
  refine length_comap_eq ((WL X ka la).subtype.restrictScalars (X.Ol la)) ?_ (N ⊓ X.ofK la V')
    (N' ⊓ X.ofK la V') ?_
  · exact Subtype.val_injective
  · intro x hx
    exact ⟨⟨x, hV' hx.2⟩, rfl⟩


end Formalism.MainNotions.Gaps.T0
end
end

section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}


end Formalism.MainNotions.Gaps.T0
end
end

section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}



end Formalism.MainNotions.Gaps.T0
end
end

section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem phiC_nonneg (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    0 ≤ X.phiC la y := by
  unfold PJ.phiC
  split_ifs with h
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    unfold ModuliIntegralCharts.Loc.phiCy ModuliIntegralCharts.phiC
    refine Real.sInf_nonneg ?_
    rintro x ⟨l, -, h2, rfl⟩
    by_cases hb : (P.loc X.dat (resCh la)).beS (X.pt66 la y) = 0
    · rw [hb]; simp
    · refine (h2 _ ?_ hb).le
      intro a
      by_cases ha : a = 0
      · subst ha; simp
      · exact ((P.loc X.dat (resCh la)).be_pos (X.pt66 la y) a ha).le
  · exact le_rfl

abbrev trivDat (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (ϖ : X.Ol la) : LocDat X ka la where
  O' := X.Ol la
  K' := X.Kl la
  V₁ := ↥(WL X ka la)
  bc := LinearMap.id
  ϖ := ϖ
  K₁ := X.Kl la
  ι := Empty
  y := Empty.elim
  ν := Empty.elim
  ep := Empty.elim
  f := Empty.elim
  R := 0
  I := 0
  N₁ := ⊥
  Z := ThW X S ka wL wF T la
  Zm := MW X ka la
  N' := MW X ka la
  n := 0
  be := 0
  th := Fin.elim0
  c := 0
  Wsec := PUnit
  AA := ⊥
  AA' := ⊥
  N₁' := ⊥
  ρ := 0
  a := 1
  a' := 1
  Rr := fun _ => X.Ol la
  Aq := fun _ => X.Ol la
  hR := fun z => z.elim
  xq := fun _ => 0
  nq := fun _ => 0
  Fq := fun _ _ => ⊥
  rq := fun _ _ => 0
  A0 := PUnit
  n1 := 0
  F1 := fun _ => ⊤
  ι1 := Empty
  deg := Empty.elim
  δ := 0
  t := Fin.elim0
  σ := fun _ => 0
  u := Empty.elim

theorem up_trivDat (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (ϖ : X.Ol la) (N : Submodule (X.Ol la) ↥(WL X ka la)) :
    (trivDat X S ka wL wF T la ϖ).up N = N := by
  rw [LocDat.up]
  have himg : ((trivDat X S ka wL wF T la ϖ).bc '' (N : Set ↥(WL X ka la))) = (N : Set ↥(WL X ka la)) :=
    Set.image_id _
  rw [himg]
  exact Submodule.span_eq N

theorem subsingleton_quot {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton M]
    (N : Submodule R M) : Subsingleton (M ⧸ N) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N a
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N b
  rw [Subsingleton.elim x y]

theorem triv_ok (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T e : ℕ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (ϖ : X.Ol la) (hϖ : Irreducible ϖ)
    (hL : InLat X ka la S wL wF T) (hle : ThW X S ka wL wF T la ≤ MW X ka la) :
    (trivDat X S ka wL wF T la ϖ).Ok S wL wF T e := by
  refine ⟨hL, ⟨?_, hϖ, hϖ⟩, fun z => z.elim, ?_, ?_, ?_⟩
  · exact IsBaseChange.ofEquiv (LinearEquiv.refl (X.Kl la) ↥(WL X ka la))
  · unfold LocDat.InRes
    rw [up_trivDat, up_trivDat]
    dsimp (config := {instances := true}) only [trivDat]
    have hspan : Submodule.span (X.Kl la)
        (((⊥ : Submodule (X.Ol la) ↥(WL X ka la)) ⊔ ThW X S ka wL wF T la :
          Submodule (X.Ol la) ↥(WL X ka la)) : Set ↥(WL X ka la)) = ⊤ := by
      rw [bot_sup_eq]; exact hL.2.2
    refine ⟨?_, fun i => i.elim0, fun i => i.elim0, ?_, ?_, fun _ _ i => i.elim0, one_ne_zero,
      one_ne_zero, ?_, ?_, bot_le, hle, le_rfl, ?_, ?_, ?_, le_rfl, le_rfl, ?_⟩
    · rw [bot_sup_eq]
    · rw [hspan]; exact le_top
    · rw [LinearMap.ker_zero, top_sup_eq]
    · simp
    · refine inf_le_left.trans ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (MW X ka la).smul_mem _ hx
    · intro x; simp
    · rw [LinearMap.ker_zero]; simp
    · exact Subsingleton.elim _ _
    · exact Formalism.LatticeIndexTer.latFinite _ (X.Kl la) _ _ _ hL.1 hL.2
  · refine ⟨fun z => z.elim, fun z => z.elim, fun z => z.elim, fun z => z.elim, fun z => z.elim,
      fun z => z.elim, fun z => z.elim, ?_⟩
    dsimp (config := {instances := true}) only [trivDat]
    have := subsingleton_quot
      ((⊥ : Submodule (X.Ol la) PUnit).comap (⊥ : Submodule (X.Ol la) PUnit).subtype)
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  · unfold LocDat.InLead
    dsimp (config := {instances := true}) only [trivDat]
    refine ⟨rfl, Subsingleton.elim _ _, fun _ => le_rfl, fun _ => Subsingleton.elim _ _,
      fun _ y => ⟨0, Subsingleton.elim _ _⟩, fun α => α.elim, fun α => α.elim,
      linearIndependent_empty_type, Subsingleton.elim _ _, rfl, ?_⟩
    rw [Nat.cast_zero, Module.length_eq_zero_iff]
    exact subsingleton_quot _



namespace LocDat

variable {X : PJ D B P j} {ka : WeightFamilies.Wt D j} {la : HeightOneSpectrum (𝓞 B.KO)} (L : LocDat X ka la)

def InTieW (S : Scal B) (wL : WeightFamilies.Wt D j) : Prop :=
  ∀ z, ((L.ν z : ℝ) : EReal) ≤ X.depth S.sW wL la (L.y z) ∧ (∃ m : ℤ, (L.ep z : ℝ) * L.ν z = m) ∧
    1 ≤ L.ep z

def OkW (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T e : ℕ) : Prop :=
  InLat X ka la S wL wF T ∧ L.InExt ∧ L.InTieW S wL ∧ L.InRes S wL wF T e ∧ L.InPts T e ∧ L.InLead

variable {L}

theorem InTie.toW {S : Scal B} {wL : WeightFamilies.Wt D j} (h : L.InTie S wL) : L.InTieW S wL := by
  intro z
  obtain ⟨h1, h2, h3, -⟩ := h z
  exact ⟨h1.symm.le, h2, h3⟩

theorem Ok.toW {S : Scal B} {wL wF : WeightFamilies.Wt D j} {T e : ℕ} (h : L.Ok S wL wF T e) :
    L.OkW S wL wF T e := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact (show _ ∧ _ ∧ _ ∧ _ from ⟨h1, h2, InTie.toW h3, h4⟩)

end LocDat



def Thm0LocalW : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (la : HeightOneSpectrum (𝓞 B.KO)) (e : ℕ),
    H1 large₂ X H S wL nus → 1 ≤ T →
    X.Theta S ka wL wF T ≤ X.Msup ka →
    (T : ℝ) * nus la ≤ (e : ℝ) →
    ∀ L : LocDat X ka la, L.OkW S wL wF T e →
    ∀ V' : Submodule (X.Kl la) (X.Vl la), V' ≤ X.locK la (X.Msup ka) →
      X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
          (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
          (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
        (e : ℝ) * (finrank (X.Kl la) V' : ℝ) + L.err T (max 0 (cc D large₂ H.Cc H.Ac H.CRc wL))



def Thm0ConclW : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) (r : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    H1 large₂ X H S wL nus → 1 ≤ T →
    X.Theta S ka wL wF T ≤ X.Msup ka →
    (∀ la, 0 ≤ r la) → Summable (fun la => r la * X.lN la) → (∑' la, r la * X.lN la) ≤ β →
    (∀ la (e : ℕ), (T : ℝ) * nus la ≤ (e : ℝ) →
      ∃ L : LocDat X ka la, L.OkW S wL wF T e ∧
        L.err T (max 0 (cc D large₂ H.Cc H.Ac H.CRc wL)) ≤ r la) →
    Concl X S ka wL wF T nus β



end Formalism.MainNotions.Gaps.T0
end
end
