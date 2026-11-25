module

public import Formalism.LocalToGlobal.InertKernelTheory.StatementAdmAt
public import Formalism.LocalToGlobal.InertKernelTheory.TranslatesOfInertKernelAtPlace
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelInstances
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoupledSumOfEntries
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
public import Formalism.LocalToGlobal.InertKernelTheory.AdmissibleEleventhInert
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FirstKernelSmallOfFrameTwist
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.LatticeShapeMiddleHolds
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PositivityConditionHolds
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelNonzeroUnit
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LowestInvariantLeDelta
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TminusLinApply
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HkLatTupUpdate
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WeightUpdateAtPlace
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NatCastInvMemRp
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DescentCore
public import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel

section
@[expose] public section

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelCoupled

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}
variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)
variable (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)

def LatC (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) : Prop :=
  ∀ x, (X.Pj j).IsLatTup (lp x).2

def DegreeCompatibilityAtLevel (j : ℕ) : Prop :=
  ∀ x : (D.chTw u μ).cls j, padicValNat p (Nat.card ((D.chTw u μ).stab j x)) ≤ X.dG j

def TieSerC (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) :
    Prop :=
  ∀ (x : (D.chTw u μ).cls j) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    Y.ThF j (lp x) (c', L') = ((Y.eS j (lp x) * (Y.eT j (c', L'))⁻¹)⁻¹ : X.G.Kf) • Sr j (lp x) (c', L')

def KernelDifferenceWithConstant {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) (cK : Y.Kc) :
    Prop :=
  ∀ (x : (D.chTw u μ).cls j) (y : ((ex.tw.fm u μ).lat j).V) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup),
    (X.Pj (j + 1)).IsLatTup L' →
      Rd j c' L' (entRec t ex.tw u μ j x y) = cK • Y.DelF j (cmp j y (lp x).1 (lp x).2) (Sr j (lp x) (c', L'))

def HeckeC (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) : Prop :=
  ∀ (v : X.Pl) (i : ℕ), ∀ F ∈ X.FQ j, ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∑ x : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j x) : ℕ) : Y.Kc))⁻¹ •
        ∑ᶠ (L1 : Submodule ((X.Pj j).W (X.vJ j v)) (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq (X.vJ j v)))
          (_ : IsEdge p ((X.Pj j).n' (X.vJ j v)) i ⟨(lp x).2 (X.vJ j v), L1⟩),
          Y.ker j ((lp x).1, Function.update (lp x).2 (X.vJ j v) L1) La' (F (lp x).1 (lp x).2) =
      ∑ x : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j x) : ℕ) : Y.Kc))⁻¹ •
        Y.ker j (lp x) La' (X.Tm v i j F (lp x).1 (lp x).2)

def TiesC {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) : Prop :=
  FormsSharpAt t u μ j ∧ TieReadAt (Y := Y) u μ cmp ι Rd j ∧ LatC u μ j lp ∧ DegreeCompatibilityAtLevel (X := X) u μ j ∧ TieSerC Y u μ Sr j lp ∧
    ∃ cK : Y.Kc, cK ∈ Y.Oc ∧ cK⁻¹ ∈ Y.Oc ∧ cK ≠ 0 ∧ KernelDifferenceWithConstant Y t u μ cmp ι Rd Sr j lp cK

def SecC (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) : Prop :=
  ∀ x, lp x ∈ Y.Rep j ∧ cls j (lp x).1 (lp x).2 = x

end Gen

def SecondKernelCoupledLastLift : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (ι : ℂ →+* Y.Kc) (Rd : _) (Sr : _)
    (lp : (D.chTw u μ).cls (D.R.m - 1) → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (D.R.m - 1)),
    0 < D.R.m → TiesC Y t u μ KA.cmp ι Rd Sr (D.R.m - 1) lp → HeckeC Y u μ (D.R.m - 1) lp →
      ExpansionDecomposition D _ Y (D.R.m - 1)

def Adm4NewInst : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (ι : ℂ →+* Y.Kc) (Rd : _) (Sr : _)
    (lp : (D.chTw u μ).cls (D.R.m - 1) → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (D.R.m - 1)),
    (∀ j, j + 1 < D.R.m → TiesAt t u μ KA.cls KA.cmp ι Rd Sr j) →
    (0 < D.R.m → TiesC Y t u μ KA.cmp ι Rd Sr (D.R.m - 1) lp ∧ HeckeC Y u μ (D.R.m - 1) lp) →
      ArchimedeanSignatureMatching D _ Y

def HeckeCEntry : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om))
    (lp : (D.chTw u μ).cls (D.R.m - 1) → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (D.R.m - 1)),
    0 < D.R.m → MinkowskiCounting D _ Y → SecC Y u μ KA.cls (D.R.m - 1) lp → TieStabAt (Y := Y) u μ KA.cls (D.R.m - 1) →
      HeckeC Y u μ (D.R.m - 1) lp

def TiesCOfAt : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (ι : ℂ →+* Y.Kc) (Rd : _) (Sr : _)
    (lp : (D.chTw u μ).cls (D.R.m - 1) → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (D.R.m - 1)),
    0 < D.R.m → SecC Y u μ KA.cls (D.R.m - 1) lp → TiesAt t u μ KA.cls KA.cmp ι Rd Sr (D.R.m - 1) →
      TiesC Y t u μ KA.cmp ι Rd Sr (D.R.m - 1) lp

def SecCEx : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)),
    0 < D.R.m → ∃ lp, SecC Y u μ KA.cls (D.R.m - 1) lp

end Formalism.L2.KerInert.SecondKernelCoupled
end
end
end


section
@[expose] public section

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Classical

section Abstract

variable {Γ A K : Type} [Group Γ] [Field K] [CharZero K] (sm : Γ → A → A)
  (h1 : ∀ a, sm 1 a = a) (hm : ∀ γ γ' a, sm (γ * γ') a = sm γ (sm γ' a))

include h1 hm in
theorem sm_inv_sm (γ : Γ) (a : A) : sm γ⁻¹ (sm γ a) = a := by rw [← hm, inv_mul_cancel, h1]

def fibEquiv (b0 : A) (γ0 : Γ) : {γ : Γ // sm γ b0 = sm γ0 b0} ≃ {γ : Γ // sm γ b0 = b0} where
  toFun γ := ⟨γ0⁻¹ * γ.1, by rw [hm, γ.2, sm_inv_sm sm h1 hm]⟩
  invFun γ := ⟨γ0 * γ.1, by rw [hm, γ.2]⟩
  left_inv γ := Subtype.ext (mul_inv_cancel_left γ0 γ.1)
  right_inv γ := Subtype.ext (inv_mul_cancel_left γ0 γ.1)

include h1 hm in
theorem T_finite (b0 : A) (hfin : Finite {γ : Γ // sm γ b0 = b0}) (B : Finset A) : {γ : Γ | sm γ b0 ∈ B}.Finite := by
  have e : {γ : Γ | sm γ b0 ∈ B} = ⋃ b ∈ B, {γ | sm γ b0 = b} := by
    ext γ
    simp
  rw [e]
  refine Set.Finite.biUnion B.finite_toSet (fun b _ => ?_)
  by_cases h : ∃ γ0, sm γ0 b0 = b
  · obtain ⟨γ0, rfl⟩ := h
    exact Set.finite_coe_iff.1 (Finite.of_equiv _ (fibEquiv sm h1 hm b0 γ0).symm)
  · exact Set.finite_empty.subset (fun γ hγ => (h ⟨γ, hγ⟩).elim)

include h1 hm in
theorem orbit_sum_stabilizer (b0 : A) (B : Finset A) (f : A → K) (T : Finset Γ) (hT : ∀ γ, γ ∈ T ↔ sm γ b0 ∈ B) :
    ∑ γ ∈ T, f (sm γ b0) =
      (Nat.card {γ : Γ // sm γ b0 = b0} : K) * ∑ b ∈ B.filter (fun b => ∃ γ, b = sm γ b0), f b := by
  rw [Finset.sum_comp f (fun γ => sm γ b0), Finset.mul_sum]
  have himg : T.image (fun γ => sm γ b0) = B.filter (fun b => ∃ γ, b = sm γ b0) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨(hT γ).1 hγ, γ, rfl⟩
    · rintro ⟨hb, γ, rfl⟩
      exact ⟨γ, (hT γ).2 hb, rfl⟩
  rw [himg]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  obtain ⟨hbB, γ0, rfl⟩ := Finset.mem_filter.1 hb
  rw [nsmul_eq_mul, ← Nat.card_congr (fibEquiv sm h1 hm b0 γ0)]
  congr 2
  refine (Nat.subtype_card _ (fun γ => ?_)).symm
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨(hT γ).2 ?_, h⟩
    rw [h]
    exact hbB

theorem sum_orb (S : A → Prop) (Rp : Finset A) (hex : ∀ a, S a → ∃! a0, a0 ∈ Rp ∧ ∃ γ, a = sm γ a0) (B : Finset A)
    (hB : ∀ b ∈ B, S b) (f : A → K) :
    ∑ b ∈ B, f b = ∑ b0 ∈ Rp, ∑ b ∈ B.filter (fun b => ∃ γ, b = sm γ b0), f b := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  obtain ⟨a0, ⟨h0, hγ⟩, huniq⟩ := hex b (hB b hb)
  rw [Finset.sum_eq_single a0]
  · rw [ite_eq_left hγ]
  · intro c hc hne
    rw [ite_eq_right]
    intro h
    exact hne (huniq c ⟨hc, h⟩)
  · intro h
    exact absurd h0 h

def TT (b0 : A) (hfin : Finite {γ : Γ // sm γ b0 = b0}) (B : Finset A) : Finset Γ :=
  (T_finite sm h1 hm b0 hfin B).toFinset

theorem mem_TT (b0 : A) (hfin : Finite {γ : Γ // sm γ b0 = b0}) (B : Finset A) (γ : Γ) :
    γ ∈ TT sm h1 hm b0 hfin B ↔ sm γ b0 ∈ B := Set.Finite.mem_toFinset _


include h1 hm in
theorem sum_unfold (S : A → Prop) (Rp : Finset A) (hRp : ∀ a ∈ Rp, S a)
    (hex : ∀ a, S a → ∃! a0, a0 ∈ Rp ∧ ∃ γ, a = sm γ a0)
    (hst : ∀ a, S a → 0 < Nat.card {γ : Γ // sm γ a = a}) (B : Finset A) (hB : ∀ b ∈ B, S b) (f : A → K) :
    ∑ b ∈ B, f b = ∑ b0 ∈ Rp.attach, (Nat.card {γ : Γ // sm γ b0.1 = b0.1} : K)⁻¹ *
      ∑ γ ∈ TT sm h1 hm b0.1 (Nat.card_pos_iff.1 (hst b0.1 (hRp b0.1 b0.2))).2 B, f (sm γ b0.1) := by
  rw [sum_orb sm S Rp hex B hB f, ← Finset.sum_attach]
  refine Finset.sum_congr rfl (fun b0 _ => ?_)
  rw [orbit_sum_stabilizer sm h1 hm b0.1 B f _ (mem_TT sm h1 hm b0.1 _ B), ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Nat.cast_ne_zero.2 (hst b0.1 (hRp b0.1 b0.2)).ne'


include h1 hm in
theorem adj (S : A → Prop) (Rp : Finset A) (hRp : ∀ a ∈ Rp, S a)
    (hex : ∀ a, S a → ∃! a0, a0 ∈ Rp ∧ ∃ γ, a = sm γ a0)
    (hst : ∀ a, S a → 0 < Nat.card {γ : Γ // sm γ a = a})
    (R : A → A → Prop) (hR : ∀ γ a b, R a b → R (sm γ a) (sm γ b)) (hRS : ∀ a b, R a b → (S a ↔ S b))
    (up dn : A → Finset A) (hup : ∀ a, S a → ∀ b, b ∈ up a ↔ R a b) (hdn : ∀ b, S b → ∀ a, a ∈ dn b ↔ R a b)
    (φ : A → A → K) (hφ : ∀ γ a b, φ (sm γ a) (sm γ b) = φ a b) :
    ∑ a ∈ Rp, (Nat.card {γ : Γ // sm γ a = a} : K)⁻¹ * ∑ b ∈ up a, φ a b =
      ∑ b ∈ Rp, (Nat.card {γ : Γ // sm γ b = b} : K)⁻¹ * ∑ a ∈ dn b, φ a b := by
  have hL : ∀ a ∈ Rp, (Nat.card {γ : Γ // sm γ a = a} : K)⁻¹ * ∑ b ∈ up a, φ a b =
      ∑ b0 ∈ Rp.attach, (Nat.card {γ : Γ // sm γ a = a} : K)⁻¹ * ((Nat.card {γ : Γ // sm γ b0.1 = b0.1} : K)⁻¹ *
        ∑ γ ∈ TT sm h1 hm b0.1 (Nat.card_pos_iff.1 (hst b0.1 (hRp b0.1 b0.2))).2 (up a), φ a (sm γ b0.1)) := by
    intro a ha
    rw [sum_unfold sm h1 hm S Rp hRp hex hst (up a)
      (fun b hb => (hRS a b ((hup a (hRp a ha) b).1 hb)).1 (hRp a ha)) (φ a), Finset.mul_sum]
  have hRr : ∀ b ∈ Rp, (Nat.card {γ : Γ // sm γ b = b} : K)⁻¹ * ∑ a ∈ dn b, φ a b =
      ∑ a0 ∈ Rp.attach, (Nat.card {γ : Γ // sm γ b = b} : K)⁻¹ * ((Nat.card {γ : Γ // sm γ a0.1 = a0.1} : K)⁻¹ *
        ∑ γ ∈ TT sm h1 hm a0.1 (Nat.card_pos_iff.1 (hst a0.1 (hRp a0.1 a0.2))).2 (dn b), φ (sm γ a0.1) b) := by
    intro b hb
    rw [sum_unfold sm h1 hm S Rp hRp hex hst (dn b)
      (fun a ha => (hRS a b ((hdn b (hRp b hb) a).1 ha)).2 (hRp b hb)) (fun a => φ a b), Finset.mul_sum]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hRr, ← Finset.sum_attach Rp, ← Finset.sum_attach Rp, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  rw [← mul_assoc, ← mul_assoc, mul_comm ((Nat.card {γ : Γ // sm γ a.1 = a.1} : K)⁻¹)]
  congr 1
  refine Finset.sum_nbij' (fun γ => γ⁻¹) (fun γ => γ⁻¹) ?_ ?_ (fun γ _ => inv_inv γ) (fun γ _ => inv_inv γ) ?_
  · intro γ hγ
    rw [mem_TT] at hγ ⊢
    have h2 := hR γ⁻¹ _ _ ((hup a.1 (hRp a.1 a.2) _).1 hγ)
    rw [sm_inv_sm sm h1 hm] at h2
    exact (hdn b.1 (hRp b.1 b.2) _).2 h2
  · intro γ hγ
    rw [mem_TT] at hγ ⊢
    have h2 := hR γ⁻¹ _ _ ((hdn b.1 (hRp b.1 b.2) _).1 hγ)
    rw [sm_inv_sm sm h1 hm] at h2
    exact (hup a.1 (hRp a.1 a.2) _).2 h2
  · intro γ _
    rw [← hφ γ⁻¹ a.1 (sm γ b.1), sm_inv_sm sm h1 hm]

end Abstract

section Conc

open Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf} (C : Level P) (v : Fin P.nV) (i : ℕ)

def upd (L : P.Tup) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) : P.Tup :=
  Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A

theorem upd_self (L : P.Tup) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) : upd v L A v = A :=
  Function.update_self (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) v A L

theorem upd_ne (L : P.Tup) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) {u : Fin P.nV} (h : u ≠ v) :
    upd v L A u = L u :=
  Function.update_of_ne (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) h A L

theorem upd_inj (L : P.Tup) : Function.Injective (upd v L) := by
  intro A B h
  simpa [upd_self] using congrFun h v

def Rel (L L1 : P.Tup) : Prop := IsEdge p (P.n' v) i ⟨L v, L1 v⟩ ∧ ∀ u, u ≠ v → L u = L1 u

theorem Rel_smul (γ : C.Γ) (L L1 : P.Tup) (h : Rel v i L L1) : Rel v i (C.smul γ L) (C.smul γ L1) := by
  refine ⟨nt_edge_map p (P.n' v) i (C.act v γ) (L v) (L1 v) h.1, fun u hu => ?_⟩
  show (L u).map _ = (L1 u).map _
  rw [h.2 u hu]

theorem Rel_lat (L L1 : P.Tup) (h : Rel v i L L1) : P.IsLatTup L ↔ P.IsLatTup L1 := by
  constructor
  · intro hL u
    by_cases hu : u = v
    · subst hu
      exact h.1.2.1
    · rw [← h.2 u hu]
      exact hL u
  · intro hL u
    by_cases hu : u = v
    · subst hu
      exact h.1.1
    · rw [h.2 u hu]
      exact hL u

def upS (L : P.Tup) : Finset P.Tup := (UP P v i (L v)).image (upd v L)

def dnS (L1 : P.Tup) : Finset P.Tup := (EE P v i (L1 v)).image (upd v L1)

theorem mem_upS (L L1 : P.Tup) : L1 ∈ upS v i L ↔ Rel v i L L1 := by
  unfold upS
  rw [Finset.mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨by simpa [upd_self] using (mem_UP P).1 hA, fun u hu => (upd_ne v L A hu).symm⟩
  · intro h
    refine ⟨L1 v, (mem_UP P).2 h.1, ?_⟩
    exact Function.update_eq_iff.mpr ⟨rfl, h.2⟩

theorem mem_dnS (L L1 : P.Tup) : L ∈ dnS v i L1 ↔ Rel v i L L1 := by
  unfold dnS
  rw [Finset.mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨by simpa [upd_self] using (mem_EE P).1 hA, fun u hu => upd_ne v L1 A hu⟩
  · intro h
    refine ⟨L v, (mem_EE P).2 h.1, ?_⟩
    exact Function.update_eq_iff.mpr ⟨rfl, fun u hu => (h.2 u hu).symm⟩

theorem adj_level {K : Type} [Field K] [CharZero K] (Rc : Finset P.Tup) (hlat : ∀ L ∈ Rc, P.IsLatTup L)
    (hex : ∀ L, P.IsLatTup L → ∃! L0, L0 ∈ Rc ∧ ∃ γ : C.Γ, L = C.smul γ L0)
    (hst : ∀ L, P.IsLatTup L → 0 < Nat.card {γ : C.Γ // C.smul γ L = L})
    (φ : P.Tup → P.Tup → K) (hφ : ∀ (γ : C.Γ) L L1, φ (C.smul γ L) (C.smul γ L1) = φ L L1) :
    ∑ L ∈ Rc, (Nat.card {γ : C.Γ // C.smul γ L = L} : K)⁻¹ *
        ∑ᶠ (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (_ : IsEdge p (P.n' v) i ⟨L v, A⟩),
          φ L (Function.update L v A) =
      ∑ L1 ∈ Rc, (Nat.card {γ : C.Γ // C.smul γ L1 = L1} : K)⁻¹ *
        ∑ᶠ (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (_ : IsEdge p (P.n' v) i ⟨A, L1 v⟩),
          φ (Function.update L1 v A) L1 := by
  have e1 : ∀ L : P.Tup, ∑ᶠ (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (_ : IsEdge p (P.n' v) i ⟨L v, A⟩),
      φ L (Function.update L v A) = ∑ L1 ∈ upS v i L, φ L L1 := by
    intro L
    unfold upS
    rw [Finset.sum_image (fun a _ b _ h => upd_inj v L h)]
    exact finsum_mem_eq_finite_toFinset_sum _ (up_fin P v i (L v))
  have e2 : ∀ L1 : P.Tup, ∑ᶠ (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (_ : IsEdge p (P.n' v) i ⟨A, L1 v⟩),
      φ (Function.update L1 v A) L1 = ∑ L ∈ dnS v i L1, φ L L1 := by
    intro L1
    unfold dnS
    rw [Finset.sum_image (fun a _ b _ h => upd_inj v L1 h)]
    exact finsum_mem_eq_finite_toFinset_sum _ (edges_fin P v i (L1 v))
  simp_rw [e1, e2]
  exact adj C.smul (lsmul_one C) (_root_.Formalism.MainNotions.G.LatticeSystems.jd_smul_mul C) P.IsLatTup Rc hlat hex hst (Rel v i) (Rel_smul C v i) (Rel_lat v i)
    (upS v i) (dnS v i) (fun L _ L1 => mem_upS v i L L1) (fun L1 _ L => mem_dnS v i L L1) φ hφ

end Conc

section Final

variable {p : ℕ} [Fact p.Prime]

theorem up_down_adjoint (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) : Formalism.MainNotions.FormalGroupSystem.adm6 D X Y := by
  intro j hj v' i φ hφ
  have : CharZero Y.Kc := Formalism.MainNotions.FormalGroupSystem.Pf.charZero_K' p Y.Kc

  let Rc : X.Lv.comp j → Finset (X.Pj j).Tup := fun c => ((Y.Rep j).filter fun La => La.1 = c).image Prod.snd
  have hRc : ∀ c L, L ∈ Rc c ↔ (c, L) ∈ Y.Rep j := by
    intro c L
    simp only [Rc, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨c', L'⟩, ⟨h1, h2⟩, h3⟩
      cases h2
      cases h3
      exact h1
    · intro h
      exact ⟨(c, L), ⟨h, rfl⟩, rfl⟩
  have split : ∀ F : X.Lt j → Y.Kc, ∑ La ∈ Y.Rep j, F La =
      ∑ c ∈ (Y.Rep j).image Prod.fst, ∑ L ∈ Rc c, F (c, L) := by
    intro F
    rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := (Y.Rep j).image Prod.fst)
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Rc]
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl (fun x hx => ?_)
      obtain ⟨c', L⟩ := x
      have h2 : c' = c := (Finset.mem_filter.1 hx).2
      cases h2
      rfl
    · rintro ⟨c1, L1⟩ h1 ⟨c2, L2⟩ h2 h
      have e1 : c1 = c := (Finset.mem_filter.1 h1).2
      have e2 : c2 = c := (Finset.mem_filter.1 h2).2
      cases e1
      cases e2
      cases h
      rfl
  rw [split, split]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  exact adj_level (X.Lv.lev j c) v' i (Rc c) (fun L hL => Y.Rep_lat j (c, L) ((hRc c L).1 hL))
    (fun L hL => by
      obtain ⟨L0, ⟨h0, hγ⟩, hu⟩ := Y.Rep_ex j hj c L hL
      exact ⟨L0, ⟨(hRc c L0).2 h0, hγ⟩, fun L2 h2 => hu L2 ⟨(hRc c L2).1 h2.1, h2.2⟩⟩)
    (fun L hL => Y.stab_fin j hj (c, L) hL) (φ c) (hφ c)

end Final

end Formalism.L2.G.Pend
end
end
end


-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.InertKernelTheory.ThetaSeriesDataHypothesesBelowMaximalLevel, Formalism.LocalToGlobal.InertKernelTheory.AdmissibleAllLevels, Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelCoupled, Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleEntriesOfKernelLaw

-- ===== clump member: Formalism.LocalToGlobal.InertKernelTheory.ThetaSeriesDataHypothesesBelowMaximalLevel =====
-- clump-header: {"m": "Formalism.LocalToGlobal.InertKernelTheory.ThetaSeriesDataHypothesesBelowMaximalLevel", "h": "module\n\npublic import Formalism.LocalToGlobal.InertKernelTheory.StatementAdmAt\npublic import Formalism.LocalToGlobal.InertKernelTheory.TranslatesOfInertKernelAtPlace\npublic import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelCoupledLastLift\npublic import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.AdmLoc2

open Formalism.L2.PairingIndexBounds.F
open Formalism.L2.KerInert.AdmLoc (pendG CurveIn XiIn)

section Law

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)

def StabLawLt (ThR : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  ∀ j < X.mm, ∀ (c : X.Lv.comp j) (L0 : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (ε : (X.Lv.lev j c).Γ),
    (c, L0) ∈ repOf X.Lv hfin j → (X.Pj (j + 1)).IsLatTup La'.2 → (X.Lv.lev j c).smul ε L0 = L0 →
      MvPowerSeries.C ((kapG X ℂ_[p] j c ε)⁻¹) * SA X ℂ_[p] j (gamAt X j c ε) (ThR j (c, L0) La') = ThR j (c, L0) La'

end Law

section Gen

variable {p : ℕ} [Fact p.Prime] {D : D7}

def ThetaSeriesDataHypothesesBelowMaximalLevel (X : Sys p) (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) : Prop :=
  Formalism.L2.KerInert.RepLt.AdmGLt X hfin D fd ∧ Formalism.L2.KerInert.RepRec.ClAway p cl ∧ Formalism.L2.KerInert.KGLt.XiAwayLt X hfin D Ξ₀ ∧
    Formalism.L2.KerInert.RepLt.ScalGLt X hfin fd χ muT lam ∧
    ∃ ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v,
      Formalism.L2.KerInert.RepFrame.LamPosG X E D pos lam ρ ∧ Formalism.L2.KerInert.RepFrame.MInv X fd.frM ∧
      Formalism.L2.KerInert.RepLt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La) (fun j _ La' => fd.kerN (j + 1) La') ρ

def LawInLt (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (E : CEmbC X.G)
    {g : GL3Theta.G1 p} (hLT : LTIso g) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (fd : FData X D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  StabLawLt X E.toCEmb hfin (thFOf X pos (FrecG E.toCEmb pos fd B χ lam SS cl Ξ₀ muT (ltC g hLT)))

end Gen

def AdmGen2 : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (cl : ℕ) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ),
    CurveIn D p cc δ g B χ lam → ThetaSeriesDataHypothesesBelowMaximalLevel X E hfin pos fd χ lam cl Ξ₀ muT →
    XiIn X E hfin hst hLT pos fd B χ lam SS cl Ξ₀ muT → LawInLt X hfin E hLT pos fd B χ lam SS cl Ξ₀ muT →
    adm3b D X → ArchimedeanSignatureMatching D X (pendG X E hfin hst hLT pos fd B χ lam SS cl Ξ₀ muT) →
      admitted D X (pendG X E hfin hst hLT pos fd B χ lam SS cl Ξ₀ muT)


open Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelCoupled in
def AdmAt2 : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    [IsFractionRing (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.O (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.Kf] (E : CEmbC (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G)
    (hfin : ∀ j c, ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv.lev j c).FinClasses) (hst : FinStab (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv)
    (g : GL3Theta.G1 (D.what₂.places.resChar w)) (hLT : LTIso g)
    (pos : (Σ v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl, Fin ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.n' v)) ≃ D.what₂.Tau)
    (Tw : TwForms D) (I : Formalism.MainNotions.G.CmpJ.CmpJIn Tw u μ w h Lv) (L0 : Formalism.L2.PairingIndexBounds.F.Lev0Data D u w h)
    (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1) →
      Formalism.L2.Col.HomE D.host.E (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1) (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ),
    CurveIn D (D.what₂.places.resChar w) cc δ g B χ lam →
    ThetaSeriesDataHypothesesBelowMaximalLevel (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) χ lam cl Ξ₀ muT →
    XiIn (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT →
    LawInLt (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin E hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT →
    (∃ ι Rd Sr, (∀ j, j + 1 < D.R.m → TiesAt (Y := (pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT)) t u μ KA.cls KA.cmp ι Rd Sr j) ∧
      (0 < D.R.m → ∃ lp, TiesC (pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT) t u μ KA.cmp ι Rd Sr (D.R.m - 1) lp ∧ HeckeC (pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT) u μ (D.R.m - 1) lp)) →
      admitted D (sysAt Ch std vp unif eO eO_spec dG dG_spec om) (pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT)


open Formalism.L2.KerInert.SecondKernelInstances in
def AdmAtEnt2 : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    [IsFractionRing (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.O (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.Kf] (E : CEmbC (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G)
    (hfin : ∀ j c, ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv.lev j c).FinClasses) (hst : FinStab (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv)
    (g : GL3Theta.G1 (D.what₂.places.resChar w)) (hLT : LTIso g)
    (pos : (Σ v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl, Fin ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.n' v)) ≃ D.what₂.Tau)
    (Tw : TwForms D) (I : Formalism.MainNotions.G.CmpJ.CmpJIn Tw u μ w h Lv) (L0 : Formalism.L2.PairingIndexBounds.F.Lev0Data D u w h)
    (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1) →
      Formalism.L2.Col.HomE D.host.E (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1) (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ),
    CurveIn D (D.what₂.places.resChar w) cc δ g B χ lam →
    ThetaSeriesDataHypothesesBelowMaximalLevel (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) χ lam cl Ξ₀ muT →
    XiIn (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT →
    LawInLt (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin E hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT →
    (∃ ι Rd Sr, ∀ j < D.R.m,
      TiesAt (Y := pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT) t u μ KA.cls KA.cmp ι Rd Sr j) →
      admitted D (sysAt Ch std vp unif eO eO_spec dG dG_spec om) (pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT)

end Formalism.L2.KerInert.AdmLoc2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.InertKernelTheory.ThetaSeriesDataHypothesesBelowMaximalLevel =====

-- ===== clump member: Formalism.LocalToGlobal.InertKernelTheory.AdmissibleAllLevels =====
-- clump-header: {"m": "Formalism.LocalToGlobal.InertKernelTheory.AdmissibleAllLevels", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem\npublic import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.L2.KerInert

def Adm8All : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p), Formalism.MainNotions.FormalGroupSystem.adm8 D X

theorem admissible_all_levels : Adm8All := fun D _ _ X =>
  ⟨Formalism.MainNotions.G.LatticeSystems.exponent_condition_holds D X.G, (Formalism.L2.G.Model.operators_preserve_lattices D X.G).2⟩

end Formalism.L2.KerInert
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.InertKernelTheory.AdmissibleAllLevels =====

-- ===== clump member: Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelCoupled =====
-- clump-header: {"m": "Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelCoupled", "h": "module\n\npublic import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelCoupledLastLift\npublic import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.OrbitSumStabilizer\npublic import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelInstances\nimport Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelNonzeroUnit\nimport Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated\npublic import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoupledSumOfEntries\nimport Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LowestInvariantLeDelta\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelCoupled

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}
variable {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} {u : D.what₂.Word} {μ : D.what₂.Tup}

theorem bodyC_of_span (Y : Pend X) (j : ℕ) (cK : Y.Kc) {I : Type} [Fintype I] (wt : I → Y.Kc) (La : I → X.Lt j)
    (S : Set (X.Fm j))
    (hS : ∀ F ∈ S, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ x : I, (wt x * cK) • Y.ker j (La x) (c', L') (F (La x).1 (La x).2))
    (F : X.Fm j) (hF : F ∈ Submodule.span X.G.Kf S) :
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ x : I, (wt x * cK) • Y.ker j (La x) (c', L') (F (La x).1 (La x).2) := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    intro c' L' _
    simp only [map_zero, Pi.zero_apply, ker_zero, smul_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    intro c' L' hL
    simp only [map_add (f := _), Pi.add_apply, ker_add, smul_add, Finset.sum_add_distrib, hx c' L' hL, hy c' L' hL]
  | smul a x _ hx =>
    intro c' L' hL
    simp only [map_smul, Pi.smul_apply, ker_smul]
    rw [map_smul_Kf Y, hx c' L' hL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_comm]

theorem second_kernel_coupled (t : KerEntTied ex) {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (hj : j < D.R.m)
    (lp : (D.chTw u μ).cls j → X.Lt j)
    (hspan : X.FQ j ≤ Submodule.span X.G.Kf (Set.range (cmp j))) (hrat : (ex.tw.fm u μ).KRat j)
    (hCh : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) → X.Kz j (cmp j x) = cmp (j + 1) y)
    (hT : TiesC Y t u μ cmp ι Rd Sr j lp) (hH : HeckeC Y u μ j lp) : ExpansionDecomposition D X Y j := by
  obtain ⟨hSh, hRd, hLat, hDG, hSer, cK, h1, h2, _, hDel⟩ := hT
  have body := bodyC_of_span Y j cK (fun x : (D.chTw u μ).cls j => (((Nat.card ((D.chTw u μ).stab j x) : ℕ) : Y.Kc))⁻¹) lp
    (Set.range (cmp j)) (by
      rintro _ ⟨x, rfl⟩ c' L' hL
      obtain ⟨y, hy⟩ := hrat x
      have hsum : (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) =
          ∑ c : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j c) : ℕ) : ℂ))⁻¹ • entRec t ex.tw u μ j c x := by
        have hQ := sharpQ_qOf (hSh x)
        funext c1 y1
        rw [compatible_lift_exists D L hT Gi Gl Kc0 Dx cX ex t u μ j hj _ _ hQ.1 hQ.2 c1 y1]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, entRec]

      rw [hCh x y hy, hRd y c' L' hL, hy, hsum, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smulₛₗ, map_inv₀, map_natCast, hDel c x c' L' hL,
        kernel_of_smul p X Y j (lp c) (c', L') _ (hSer c c' L' hL), mul_smul])
  refine ⟨cK, h1, h2, (D.chTw u μ).cls j, Unit, inferInstance, inferInstance,
    fun x => Nat.card ((D.chTw u μ).stab j x), fun x _ => lp x, fun x _ => hLat x,
    fun x => ⟨Nat.card_pos, hDG x⟩, ?_, ?_⟩
  · intro F hF c' L' hL
    simpa only [Finset.univ_unique, Finset.sum_singleton] using body F (hspan hF) c' L' hL
  · intro v i F hF La' hLa'
    simpa only [Finset.univ_unique, Finset.sum_singleton] using hH v i F hF La' hLa'

end Gen

theorem second_kernel_coupled_instance : SecondKernelCoupledLastLift := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp hm hTs hH
  have hj : D.R.m - 1 < D.R.m := by omega
  have hsp := fq_le_span (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cmp (D.R.m - 1) (KA.cmp_int (D.R.m - 1) hj.le)
  have hch : ∀ (x : ((ex.tw.fm u μ).lat (D.R.m - 1)).V) (y : ((ex.tw.fm u μ).lat (D.R.m - 1 + 1)).V),
      (ex.tw.fm u μ).emb (D.R.m - 1 + 1) y = (D.chTw u μ).K (D.R.m - 1) ((ex.tw.fm u μ).emb (D.R.m - 1) x) →
      (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Kz (D.R.m - 1) (KA.cmp (D.R.m - 1) x) = KA.cmp (D.R.m - 1 + 1) y :=
    fun x y hy => (KA.cmp_K (D.R.m - 1) hj x y hy).symm
  exact second_kernel_coupled (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) (Y := Y) (σ := ex.cmp.embW u w h) t KA.cmp ι Rd Sr
    (D.R.m - 1) hj lp hsp (KA.rat (D.R.m - 1) hj) hch hTs hH

theorem admissible_fourth_instance : Adm4NewInst := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp hE hL
  have hmm : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm = D.R.m := KA.fl_m
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have hl : j + 1 < D.R.m := by omega
    obtain ⟨cK, h1, h2, _, hb⟩ :=
      second_kernel_entry_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr hE j hl
    exact ⟨cK, h1, h2, hb⟩
  · have hm : 0 < D.R.m := by omega
    obtain rfl : j = D.R.m - 1 := by omega
    obtain ⟨hT1, hH1⟩ := hL hm
    exact second_kernel_coupled_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp
      hm hT1 hH1

theorem hecke_coupled_entry : HeckeCEntry := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y lp hm h5b hsec hst
    v i F hF La' hLa'
  have hj : D.R.m - 1 < (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm :=
    lt_of_lt_of_eq (by omega : D.R.m - 1 < D.R.m) KA.fl_m.symm
  let X := sysAt Ch std vp unif eO eO_spec dG dG_spec om
  letI := X.G.ringO
  letI := X.G.domO
  letI := X.G.dvrO
  letI := X.G.fieldK
  letI := X.G.algOK
  letI := Y.algKf
  have h6 := Formalism.L2.G.Pend.up_down_adjoint D _ Y
  have hk0 (j : ℕ) (hj : j < X.mm) (v : X.Pl) (k : ℕ)
      (F : X.Fm j) (hF : F ∈ X.FQ j) (La' : X.Lt (j + 1)) (hLa' : (X.Pj (j + 1)).IsLatTup La'.2) :
      ∑ La ∈ Y.Rep j, ((X.stab j La : X.G.Kf))⁻¹ •
        ∑ A1 ∈ Pf.UP (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
          Y.ker j (La.1, Function.update La.2 (X.vJ j v) A1) La' (F La.1 La.2) =
      ∑ La ∈ Y.Rep j, ((X.stab j La : X.G.Kf))⁻¹ • Y.ker j La La' (X.Tm v k j F La.1 La.2) := by
    open Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.G.LatticeSystems in
    classical
    apply MvPolynomial.ext
    intro n
    let φ : X.Lv.comp j → (X.Pj j).Tup → (X.Pj j).Tup → Y.Kc := fun c L L1 =>
      if (X.Pj j).IsLatTup L1 then AddMonoidAlgebra.coeff (Y.ker j (c, L1) La' (F c L)) n else 0
    have hφ : ∀ c (γ : (X.Lv.lev j c).Γ) L L1,
        φ c ((X.Lv.lev j c).smul γ L) ((X.Lv.lev j c).smul γ L1) = φ c L L1 := by
      intro c γ L L1
      simp only [φ]
      by_cases h : (X.Pj j).IsLatTup L1
      · rw [ite_eq_left h, ite_eq_left ((latTup_smul _ _ γ L1).2 h), (Eqv_of_FQ X hF).2 c γ L,
          h5b j hj c L1 La' γ (F c L) (vt_FQ X hF c L) h hLa']
      · rw [ite_eq_right h, ite_eq_right (fun h' => h ((latTup_smul _ _ γ L1).1 h'))]
    have key := h6 j hj.le (X.vJ j v) k φ hφ
    have hs : ∀ (La : X.Lt j) (z : Y.Kc), ((X.stab j La : X.G.Kf))⁻¹ • z = ((X.stab j La : Y.Kc))⁻¹ * z := by
      intro La z
      rw [Algebra.smul_def, map_inv₀, map_natCast]
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
    refine Eq.trans ?_ (key.trans ?_)
    · refine Finset.sum_congr rfl fun La hLa => ?_
      have hlat := Y.Rep_lat j La hLa
      rw [MvPolynomial.coeff_smul, hs, MvPolynomial.coeff_sum]
      congr 1
      refine Eq.trans ?_ (finsum_mem_eq_finite_toFinset_sum _ (up_fin (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)))).symm
      refine Finset.sum_congr rfl fun A1 hA1 => ?_
      have hE := (mem_UP _).1 hA1
      simp only [φ]
      rw [ite_eq_left (hk_latTup_update _ hlat _ A1 hE.2.1)]
    · refine Finset.sum_congr rfl fun La hLa => ?_
      have hlat := Y.Rep_lat j La hLa
      rw [MvPolynomial.coeff_smul, hs]
      congr 1
      refine Eq.trans (finsum_mem_eq_finite_toFinset_sum _ (edges_fin (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)))) ?_
      have e : X.Tm v k j F La.1 La.2 = ∑ L0 ∈ EE (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
          F La.1 (Function.update La.2 (X.vJ j v) L0) := Tminus_eq (X.Pj j) (X.vJ j v) k (F La.1) La.2
      rw [e, ker_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun L0 _ => ?_
      simp only [φ]
      rw [ite_eq_left hlat]
  have hk := hk0 (D.R.m - 1) hj v i F hF La' hLa'
  have hs : ∀ (n : ℕ) (z : XspC (X.Pj (D.R.m - 1 + 1)) Y.Kc), ((n : X.G.Kf))⁻¹ • z = ((n : Y.Kc))⁻¹ • z := by
    intro n z
    rw [← algebraMap_smul Y.Kc ((n : X.G.Kf))⁻¹ z, map_inv₀, map_natCast]
  simp only [hs] at hk
  have hk := ((Finset.sum_coe_sort (Y.Rep (D.R.m - 1)) _).trans hk).trans (Finset.sum_coe_sort (Y.Rep (D.R.m - 1)) _).symm
  simp only [Pf.up_finsum]
  have hb : ClsBij (Y := Y) u μ KA.cls (D.R.m - 1) :=
    class_bijection_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y (D.R.m - 1)
      (by omega)
  have hbij : Function.Bijective fun x : (D.chTw u μ).cls (D.R.m - 1) =>
      (⟨lp x, (hsec x).1⟩ : {La // La ∈ Y.Rep (D.R.m - 1)}) := by
    constructor
    · intro x1 x2 he
      have h1 := (hsec x1).2
      have h2 := (hsec x2).2
      have : lp x1 = lp x2 := congrArg Subtype.val he
      rw [← h1, ← h2, this]
    · intro La
      refine ⟨KA.cls (D.R.m - 1) La.1.1 La.1.2, ?_⟩
      apply hb.1
      show KA.cls (D.R.m - 1) (lp _).1 (lp _).2 = KA.cls (D.R.m - 1) La.1.1 La.1.2
      exact (hsec _).2
  have hw : ∀ x : (D.chTw u μ).cls (D.R.m - 1),
      Nat.card ((D.chTw u μ).stab (D.R.m - 1) x) = (sysAt Ch std vp unif eO eO_spec dG dG_spec om).stab (D.R.m - 1) (lp x) := by
    intro x
    have e := hst (lp x) (hsec x).1
    rw [(hsec x).2] at e
    exact e
  refine (Fintype.sum_bijective _ hbij _ _ fun x => ?_).trans (hk.trans (Fintype.sum_bijective _ hbij _ _ fun x => ?_).symm)
  · simp only [hw x]
    rfl
  · simp only [hw x]
    rfl

theorem coupled_compatibility_at_place : TiesCOfAt := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp hm hsec hTs
  obtain ⟨hSh, hSt, hRd, hSer, cK, h1, h2, h3, hDel⟩ := hTs
  refine ⟨hSh, hRd, fun x => Y.Rep_lat _ _ (hsec x).1, fun x => ?_, fun x c' L' hL => hSer (lp x) (hsec x).1 c' L' hL,
    cK, h1, h2, h3, fun x y c' L' hL => ?_⟩
  · have e := hSt (lp x) (hsec x).1
    rw [(hsec x).2] at e
    rw [e]
    exact dG_spec (D.R.m - 1) (by have := KA.fl_m; omega) (lp x).1 (lp x).2 (Y.Rep_lat _ _ (hsec x).1)
  · have e := hDel (lp x) (hsec x).1 y c' L' hL
    rw [(hsec x).2] at e
    exact e

theorem coupled_section_exists : SecCEx := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y hm
  have hb : ClsBij (Y := Y) u μ KA.cls (D.R.m - 1) :=
    class_bijection_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y (D.R.m - 1)
      (by omega)
  refine ⟨fun x => (Function.surjInv hb.2 x).1, fun x => ⟨(Function.surjInv hb.2 x).2, ?_⟩⟩
  exact Function.surjInv_eq hb.2 x

end Formalism.L2.KerInert.SecondKernelCoupled
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelCoupled =====

-- ===== clump member: Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleEntriesOfKernelLaw =====
-- clump-header: {"m": "Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleEntriesOfKernelLaw", "h": "module\n\npublic import Formalism.LocalToGlobal.InertKernelTheory.ThetaSeriesDataHypothesesBelowMaximalLevel\npublic import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw\npublic import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.OrbitSumStabilizer\npublic import Formalism.LocalToGlobal.InertKernelTheory.AdmissibleAllLevels\npublic import Formalism.LocalToGlobal.InertKernelTheory.AdmissibleEleventhInert\npublic import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FirstKernelSmallOfFrameTwist\npublic import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelCoupled\nimport Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelInstances\npublic import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.LatticeShapeMiddleHolds\npublic import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PositivityConditionHolds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert.AdmLoc2

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

section Law

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (be : MvPowerSeries (Fin 2) (Formalism.L2.G.Pend.K0 p))

theorem admissible_stabilizer_of_law (D : Formalism.BasicNotions.D7) (ThR : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) :
    StabLawLt X E hfin ThR → Formalism.MainNotions.FormalGroupSystem.MinkowskiCounting D X (pendR X E hfin hst be ThR) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  intro hS
  classical
  let ThR' : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p] :=
    fun j La La' => if j < X.mm ∧ (X.Pj (j + 1)).IsLatTup La'.2 then ThR j La La' else 0
  have hS' : StabLaw X ℂ_[p] hfin ThR' := by
    intro j c L0 La' ε h0 hε
    by_cases hj : j < X.mm ∧ (X.Pj (j + 1)).IsLatTup La'.2
    · simp only [ThR', ite_eq_left hj]
      exact hS j hj.1 c L0 La' ε h0 hj.2 hε
    · simp only [ThR', ite_eq_right hj]
      unfold SA
      rw [← MvPowerSeries.coe_substAlgHom (hasSubst_actS X ℂ_[p] j _), map_zero, mul_zero]
  have hK := kapLaw_of_stabLaw X ℂ_[p] hfin ThR' pC_ne_zero hS'
  intro j hj c L La' γ G hGv hL hLa'
  have hEq : ∀ La, thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR') j La La' = thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j La La' := by
    intro La
    simp only [thFN, thGeo, ThR', ite_eq_left (And.intro hj hLa')]
  have key : ∀ t : X.G.Kf,
      (eSX X j (c, (X.Lv.lev j c).smul γ L) * t) •
          delF X ℂ_[p] j ((((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O) • (X.Lv.lev j c).actX γ G)
            (thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j (c, (X.Lv.lev j c).smul γ L) La') =
        (eSX X j (c, L) * t) • delF X ℂ_[p] j G (thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j (c, L) La') := by
    intro t
    have := ker_law X ℂ_[p] pC_ne_zero (delEquivOn_GdC X ℂ_[p]) _ hK j c L La' γ G hL (vtIn_GdC X ℂ_[p] j G hGv) t
    rwa [hEq, hEq] at this
  exact key _

end Law

end Formalism.L2.KerInert.AdmLoc2

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.AdmLoc2

open Formalism.L2.PairingIndexBounds.F
open Formalism.L2.KerInert.AdmLoc (pendG CurveIn XiIn)

theorem admissible_general_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmGen2 := by
  intro D p _ X _ E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw h3b h4
  obtain ⟨h5, hAt, hin, hW, hcc, hδ, hχ, hlam, hLam⟩ := hC
  obtain ⟨hA, hcl, hXa, hS, ρ, hLP, hMI, hFL⟩ := hK
  obtain ⟨h2, h2b, h3⟩ := hK1 D p h5 X E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT ρ
    hAt hin hW hcc hδ hχ hlam hLam hA hcl hXa hS hLP hMI hFL
  refine ⟨Formalism.MainNotions.FormalGroupSystem.Pf.positivity_condition_holds D, h2, h2b, ?_, h3, h3b, h4, ?_, ?_, Formalism.L2.G.Pend.up_down_adjoint D X _,
    Formalism.L2.PairingIndexBounds.Ent.pending_tuple_admissible X E hfin hst hLT pos _ D, Formalism.L2.KerInert.admissible_all_levels D p X, ?_⟩
  · exact Formalism.L2.KerInert.admissible_second_inert D cc δ p g hLT hAt h5 hin hW X _ rfl
  · exact (invariance_iff_additive_maps_exist X E hfin hst hLT pos _ D).2 hXi
  · exact admissible_stabilizer_of_law X E.toCEmb hfin hst (beLT hLT) D _ hLaw
  · exact Formalism.L2.KerInert.admissible_eleventh_inert D cc δ p g hLT hAt h5 hin hW X _ rfl

section At

open Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelCoupled

theorem admissible_place_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmAt2 := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ E hfin hst g hLT pos
    Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw hTies
  obtain ⟨ι, Rd, Sr, hE, hL⟩ := hTies
  have hmm : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm = D.R.m := KA.fl_m
  refine admissible_general_of_kernel_law hK1 D _ (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst g hLT pos _ cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw
    (admissible_third_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om) ?_
  by_cases hm : 0 < D.R.m
  · obtain ⟨lp, hTC, hH⟩ := hL hm
    exact admissible_fourth_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ ι Rd Sr lp hE (fun _ => ⟨hTC, hH⟩)
  · exact ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega)⟩

theorem admissible_entries_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmAtEnt2 := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ E hfin hst g hLT pos
    Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw hTies
  obtain ⟨ι, Rd, Sr, hA⟩ := hTies
  have h5b := admissible_stabilizer_of_law (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E.toCEmb hfin hst (beLT hLT) D _ hLaw
  refine admissible_place_of_kernel_law hK1 D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om E hfin hst g hLT pos Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT
    hC hK hXi hLaw ⟨ι, Rd, Sr, fun j hj => hA j (by omega), fun hm => ?_⟩
  obtain ⟨lp, hsec⟩ := coupled_section_exists D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ hm
  have hT1 := hA (D.R.m - 1) (by omega)
  exact ⟨lp, coupled_compatibility_at_place D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ ι Rd Sr lp hm hsec hT1,
    hecke_coupled_entry D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ lp hm h5b hsec hT1.2.1⟩

end At

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem admissible_entries_small_chain : AdmAtEnt2 := admissible_entries_of_kernel_law Formalism.L2.KerInert.KGLt.first_kernel_law_global_small

end Formalism.L2.KerInert.AdmLoc2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleEntriesOfKernelLaw =====
