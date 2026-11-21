import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ActsRhoFin
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsPureML
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.ConeIntegralFactorisation
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.KAtCompact
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ArchCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdeleCongruenceUnitCriterion
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.IdealStmt
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FubMain
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PresOfHat

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF
open scoped Classical

def IdealM : Prop :=
  ∃ a₁ a₂ b₁ b₂ : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (r s r' s' i j i' j' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ i j → H'.IsAdapted σ B W W₁ i' j' → i < n → j < n → i' < d → j' < d →
    ∀ u (e₁ e₂ : ℤˣ), (u = shiftA H H' ∧ e₁ = a₁ ∧ e₂ = a₂) ∨ (u = shiftB σ H H' ∧ e₁ = b₁ ∧ e₂ = b₂) →
    ∃ 𝔞 : FractionalIdeal (𝓞 E)⁰ E, 𝔞 ≠ 0 ∧ (∀ v l, idem F v • u l ∈ latAtV X W v ↔ InAt 𝔞 v (l : AE F E)) ∧
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w 𝔞 = 0) ∧
      ∀ ν : Chr F E, Continuous ν → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range ν 0 → UnrOff ν (B.P : Set (Pl F)) →
        idealVal ν 𝔞 = idealVal ν H.𝔟 ^ (e₁ : ℤ) * idealVal ν H'.𝔟 ^ (e₂ : ℤ)

def FinM : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) e u ei ev, Cfg B M M₁ H H' e u → IsEvLoc M M₁ e ei ev →
    ∀ v : Pl F,
    ∀ (K : Subgroup (UA σ X.J)) (m : LocMeas K), IsStab B K → m.Is → ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' →
    ∀ (ν : Chr F E) (z : ℕ), Continuous ν → 2 ≤ z →
    ∃ Λ : Fl F v _ _ →ₗ[ℂ] Fl F v _ _, ∀ φ ∈ SB _, Λ φ = coneF B M om m v (ev v) u ν z φ ∧ Λ φ ∈ SB _ ∧ ∀ y,
      (∀ k : kAt K (evFin F v), @Integrable _ _ _ _ (borel _) (fun l : idAt E (evFin F v) =>
          ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l.1) (om (k.1, 1) Φ)) φ) y * wt ν z l.1) (m.xf v)) ∧
        Integrable (fun k : kAt K (evFin F v) => @integral _ _ _ _ (borel _) (m.xf v) fun l =>
          ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l.1) (om (k.1, 1) Φ)) φ) y * wt ν z l.1) (m.kf v)

theorem pure_ite {κ : Type} [Fintype κ] {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hw : Std w) (T : Finset (Pl F)) (f : SInf F κ)
    (A : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) :
    pure f (fun v => if v ∈ T then A v else w v) x = f (fun i => evI F (x i)) * ((∏ v ∈ T, A v fun i => evFin F v (x i)) *
      ∏ᶠ (v) (_ : v ∉ T), w v fun i => evFin F v (x i)) := by
  have e : (fun v => if v ∈ T then A v else w v) = ext w T fun v => A v := funext fun v => by
    unfold ext; split_ifs <;> rfl
  rw [e, pure_ext hw, Finset.prod_coe_sort T fun v => A v fun i => evFin F v (x i)]

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

def Concl (B : Base F E) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (om : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)) (ev : ∀ v : Pl F, Fl F v n d →ₗ[ℂ] Fl F v n₁ d₁)
    (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ) (m : LocMeas K) (U : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E))
    (ν : Chr F E) (z : ℕ) (S : Finset (Pl F)) (c₀ : ℂ) : Prop :=
  ∃ (L : SInf F _ →L[ℂ] SInf F _) (Λ : ∀ v : Pl F, Fl F v _ _ →ₗ[ℂ] Fl F v _ _) (u : Pl F → ℂ),
    IsConeI B M om m ei U ν z L ∧ (∀ f ∈ M.Pol B.ψ B.emb, L f ∈ M₁.Pol B.ψ B.emb) ∧
    (∀ v, ∀ φ ∈ SB _, Λ v φ = coneF B M om m v (ev v) U ν z φ ∧ Λ v φ ∈ SB _) ∧
    (∀ v ∉ S, u v ≠ 0 ∧ Λ v (M.vac v) = u v • M₁.vac v) ∧
    (∀ Φ ∈ schA F _, ∀ Ψ ∈ schA F _, ∀ c : ℂ, cone B M om e K μK μ U ν z (Φ + c • Ψ) =
      cone B M om e K μK μ U ν z Φ + c • cone B M om e K μK μ U ν z Ψ) ∧
    ∀ T : Finset (Pl F), S ⊆ T → ∀ (f : SInf F _) φ, (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = M.vac v) →
      (∏ v ∈ T \ S, u v) • cone B M om e K μK μ U ν z (pure f φ) = c₀ • pure (L f) fun v => if v ∈ T then Λ v (φ v) else M₁.vac v

theorem gen (hA : ActsEx) (hI : IdeleFub) (hKF : KFub) (hV : VacFixX) (hS : VacShift) (hAr : ArchCone) (hF : FinM) (hP : PureFac)
    (hSp : SchSpan) {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H H' e U ei ev} (hC : Cfg B M M₁ H H' e U)
    (hE : IsEvLoc M M₁ e ei ev) {K : Subgroup (UA σ X.J)} {μK : Measure K} {μ : Measure (AE F E)ˣ} {m : LocMeas K} (hK : IsStab B K)
    (h1 : μK.IsHaarMeasure) (h2 : μ.IsHaarMeasure) (hm : m.Is) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h0 : 𝔞 ≠ 0)
    (hlat : ∀ v l, idem F v • U l ∈ latAtV X W v ↔ InAt 𝔞 v (l : AE F E)) {z : ℕ} (hz : 2 ≤ z) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ (ν : Chr F E) (S₀ S : Finset (Pl F)), Continuous ν → S₀ ⊆ S →
      UnrOff ν (S : Set (Pl F)) → UnrOff χX (S : Set (Pl F)) → UnrOff χW (S : Set (Pl F)) →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ S → ¬ UnrAt ν w ∧ FractionalIdeal.count E w 𝔞 = 0) →
      Concl B M M₁ om e ei ev K μK μ m U ν z S (κ * (idealVal ν 𝔞 : ℂ) * charL ν (S₀ : Set (Pl F)) (z : ℂ)) := by
  obtain ⟨r₀, s₀, hX⟩ := hC.herm
  obtain ⟨πi, π, κ₁, k1, hπ, HI⟩ := hI F E σ B n X K m μ hC.base hm h2 𝔞 z h0 hz
  obtain ⟨ρi, ρ, κ₂, k2, hρ, HK⟩ := hKF F E σ B n X r₀ s₀ hC.base hX K m μK hK hm h1
  refine ⟨κ₁ * κ₂, mul_ne_zero k1 k2, fun χX χW om r s r' s' hp ν S₀ S hν hS₀ uν uX uW hram => ?_⟩
  obtain ⟨hu, HT⟩ := HI ν S₀ S hν hS₀ uν hram
  obtain ⟨L, hL, hLP, hLi⟩ := hAr F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e U ei ev hC hE K m hK hm χX χW om r s r' s' hp ν z hν (by omega)
  choose Λ hΛ using fun v => hF F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e U ei ev hC hE v K m hK hm χX χW om r s r' s' hp ν z hν hz
  have mono : ∀ {χ : Chr F E} {T : Finset (Pl F)}, S ⊆ T → UnrOff χ (S : Set (Pl F)) → UnrOff χ (T : Set (Pl F)) :=
    fun hT h w hw => h w fun h' => hw (hT h')
  let I : Fn F n d → (Fin n₁ × Fin d₁ → AF F) → K → (AE F E)ˣ → ℂ := fun Φ y k l =>
    e (M.co.rho B.ψ (U l) (om (k.1, 1) Φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z
  have main : ∀ T : Finset (Pl F), S ⊆ T → ∀ (f : SInf F _) φ, (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = M.vac v) → ∀ y,
      (∀ k, Integrable (I (pure f φ) y k) μ) ∧ Integrable (fun k => ∫ l, I (pure f φ) y k l ∂μ) μK ∧
      (∏ v ∈ T \ S, uLoc v (m.xf v) 𝔞 ν z) * ∫ k, ∫ l, I (pure f φ) y k l ∂μ ∂μK =
        (κ₁ * κ₂ * (idealVal ν 𝔞 : ℂ) * charL ν (S₀ : Set (Pl F)) (z : ℂ)) *
          pure (L f) (fun v => if v ∈ T then Λ v (φ v) else M₁.vac v) y := by
    intro T hT f φ hSB hvac y
    let t : ℂ := ∏ᶠ (v) (_ : v ∉ T), M₁.vac v fun i => evFin F v (y i)
    let gi : kAt K (evI F) → idAt E (evI F) → ℂ := fun k l =>
      ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • U l.1) (om (k.1, 1) Φ)) f) fun i => evI F (y i)
    let g : ∀ v : Pl F, kAt K (evFin F v) → idAt E (evFin F v) → ℂ := fun v k l =>
      ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • U l.1) (om (k.1, 1) Φ)) (φ v)) fun i => evFin F v (y i)
    have e1 : ∀ k l, I (pure f φ) y k l = t * (gi (ρi k) (πi l) * (∏ v ∈ T, g v (ρ v k) (π v l)) *
        (if ∀ v ∉ T, InAt 𝔞 v (l : AE F E) then 1 else 0) * wt ν z l) := fun k l => by
      have := hP F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e U ei ev hC hE K hK χX χW om r s r' s' hp T (mono hT uX) (mono hT uW) f φ hSB hvac
        k.1 k.2 l (ρi k).1 (fun v => (ρ v k).1) (πi l).1 (fun v => (π v l).1) (hρ k).1 (hρ k).2 (hπ l).1 (hπ l).2
      simp only [I, this, hlat, Pi.smul_apply, smul_eq_mul, pure_ite hC.good₁.std, wt, t, gi, g]
      ring
    have H1 := fun k : K => HT T hT (gi (ρi k)) (fun v => g v (ρ v k)) ((hLi f _).1 _) fun v _ => ((hΛ v (φ v) (hSB v)).2.2 _).1 _
    let hi : kAt K (evI F) → ℂ := fun k => @integral _ _ _ _ (borel _) m.xi fun l => gi k l * wt ν z l.1
    let h : ∀ v : Pl F, kAt K (evFin F v) → ℂ := fun v k => @integral _ _ _ _ (borel _) (m.xf v) fun l => g v k l * wt ν z l.1
    obtain ⟨i2, e2⟩ := HK T hi h (hLi f _).2 fun v _ => ((hΛ v (φ v) (hSB v)).2.2 _).2
    have hne : (∏ v ∈ T \ S, uLoc v (m.xf v) 𝔞 ν z) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v hv => (hu v (Finset.mem_sdiff.1 hv).2).1
    set p := ∏ v ∈ T \ S, uLoc v (m.xf v) 𝔞 ν z
    set c := κ₁ * (idealVal ν 𝔞 : ℂ) * charL ν (S₀ : Set (Pl F)) (z : ℂ) with hc
    have e3 : ∀ k, ∫ l, I (pure f φ) y k l ∂μ = (p⁻¹ * t * c) * (hi (ρi k) * ∏ v ∈ T, h v (ρ v k)) := fun k => by
      simp only [e1]
      rw [integral_const_mul]
      have := (H1 k).2
      apply mul_left_cancel₀ hne
      rw [mul_left_comm, this]
      field_simp
      rfl
    refine ⟨fun k => ?_, ?_, ?_⟩
    · exact ((H1 k).1.const_mul t).congr (.of_forall fun l => (e1 k l).symm)
    · simp only [e3]; exact i2.const_mul _
    · simp only [e3]
      rw [integral_const_mul, e2, pure_ite hC.good₁.std, hL]
      have e4 : ∏ v ∈ T, Λ v (φ v) (fun i => evFin F v (y i)) = ∏ v ∈ T, ∫ k, h v k ∂(m.kf v) := Finset.prod_congr rfl fun v _ => by
        rw [(hΛ v (φ v) (hSB v)).1]
        simp only [coneF, h, g, wt, mul_assoc]
      rw [e4]
      have e5 : (∫ k, @integral _ _ _ _ (borel _) m.xi (fun l =>
          ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • U l.1) (om (k.1, 1) Φ)) f) (fun i => evI F (y i)) * (ν l.1 : ℂ) *
            ((absE F E l.1 : ℝ) : ℂ) ^ z) ∂m.ki) = ∫ k, hi k ∂m.ki := by simp only [hi, gi, wt, mul_assoc]
      rw [e5, hc]
      show _ = _ * (_ * (_ * t))
      field_simp
  refine ⟨L, Λ, fun v => uLoc v (m.xf v) 𝔞 ν z, hL, hLP, fun v φ hφ => ⟨(hΛ v φ hφ).1, (hΛ v φ hφ).2.1⟩,
    fun v hv => ⟨(hu v hv).1, ?_⟩, ?_, fun T hT f φ a b => funext fun y => (main T hT f φ a b y).2.2⟩
  · rw [(hΛ v _ (hp.good.vac v).1).1]
    funext y
    have e1 : ∀ (k : kAt K (evFin F v)) (l : idAt E (evFin F v)),
        ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • U l.1) (om (k.1, 1) Φ)) (M.vac v)) =
          if InAt 𝔞 v (l.1 : AE F E) then M₁.vac v else 0 := fun k l => by
      obtain ⟨ξ, hξ, -⟩ := (hA F E σ B n d X W M χX χW om r s r' s' hp v).2.1 _ (at_idem v (U l.1)) _ (hp.good.vac v).1
      have a := hV F E σ B n d X W M χX χW om r s r' s' hp K hK v
        (fun w hw => ⟨uX w fun h => hv (hw ▸ h), uW w fun h => hv (hw ▸ h)⟩) k.1 k.2
      rw [opF_eq (hp.good.vac v).1 hξ.1 (acts_comp (om_pres hp _) a hξ.2), ← opF_eq (hp.good.vac v).1 hξ.1 hξ.2,
        hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e U ei ev hC hE v l.1]
      simp only [hlat]
    simp only [coneF, e1]
    rw [integral_const, Measure.real, (hm.kf v).2, ENNReal.toReal_one, one_smul, Pi.smul_apply, smul_eq_mul, uLoc,
      ← @integral_mul_const _ (borel _)]
    congr 1
    funext l
    split_ifs
    · rw [wt]; ring
    · simp
  · have Iadd : ∀ Φ Ψ (c : ℂ) y k l, I (Φ + c • Ψ) y k l = I Φ y k l + c * I Ψ y k l := fun Φ Ψ c y k l => by
      have : M.co.rho B.ψ (U l) (om (k.1, 1) (Φ + c • Ψ)) = M.co.rho B.ψ (U l) (om (k.1, 1) Φ) + c • M.co.rho B.ψ (U l) (om (k.1, 1) Ψ) := by
        rw [map_add, map_smul]
        funext x
        simp only [Darboux.rho, schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      simp only [I]
      rw [this, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    let Q : Fn F n d → Prop := fun Φ => ∀ y, (∀ k, Integrable (I Φ y k) μ) ∧ Integrable (fun k => ∫ l, I Φ y k l ∂μ) μK
    have inner : ∀ Φ Ψ (c : ℂ), Q Φ → Q Ψ → ∀ y k, ∫ l, I (Φ + c • Ψ) y k l ∂μ = ∫ l, I Φ y k l ∂μ + c * ∫ l, I Ψ y k l ∂μ :=
      fun Φ Ψ c a b y k => by
        simp only [Iadd]
        rw [integral_add ((a y).1 k) (((b y).1 k).const_mul c), integral_const_mul]
    have Qadd : ∀ Φ Ψ (c : ℂ), Q Φ → Q Ψ → Q (Φ + c • Ψ) := fun Φ Ψ c a b y =>
      ⟨fun k => (((a y).1 k).add (((b y).1 k).const_mul c)).congr (.of_forall fun l => (Iadd Φ Ψ c y k l).symm), by
        simp only [inner Φ Ψ c a b]; exact (a y).2.add ((b y).2.const_mul c)⟩
    have Q0 : Q 0 := fun y => by
      have : ∀ k, I 0 y k = fun _ => 0 := fun k => funext fun l => by
        have h := Iadd 0 0 1 y k l
        rw [smul_zero, add_zero, one_mul] at h
        exact left_eq_add.1 h
      simp [this]
    have QA : ∀ Φ ∈ schA F (Fin n × Fin d), Q Φ := fun Φ hΦ => by
      rw [hSp F _ M.vac (fun v => (hp.good.vac v).1) hp.good.std] at hΦ
      induction hΦ using Submodule.span_induction with
      | mem Φ h =>
        obtain ⟨f, φ, T, a, b, rfl⟩ := h
        exact fun y => let h := main (S ∪ T) Finset.subset_union_left f φ a (fun v hv => b v fun h => hv (Finset.mem_union_right _ h)) y
          ⟨h.1, h.2.1⟩
      | zero => exact Q0
      | add a b _ _ ha hb => simpa using Qadd a b 1 ha hb
      | smul c a _ ha => simpa using Qadd 0 a c Q0 ha
    intro Φ hΦ Ψ hΨ c
    funext y
    show ∫ k, ∫ l, I (Φ + c • Ψ) y k l ∂μ ∂μK = ∫ k, ∫ l, I Φ y k l ∂μ ∂μK + c * ∫ k, ∫ l, I Ψ y k l ∂μ ∂μK
    simp only [inner Φ Ψ c (QA Φ hΦ) (QA Ψ hΨ)]
    rw [integral_add (QA Φ hΦ y).2 ((QA Ψ hΨ y).2.const_mul c), integral_const_mul]

end PositivityTheory.ThKG.Loc.Cone

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem unr_div {χ χ' : Chr F E} {S : Set (Pl F)} (h : UnrOff χ S) (h' : UnrOff χ' S) : UnrOff (χ / χ') S := fun w hw x hx => by
  have a := h w hw x hx
  have b := h' w hw x hx
  have : locChar (χ / χ') w x = locChar χ w x / locChar χ' w x := map_div Circle.toUnits _ _
  rw [this, a, b, div_one]

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem nu_cont (t : IsTriple B G X om om') : Continuous X.ν := (isHecke_div t.chars.heckeα t.chars.heckeβ).1

theorem nu_res (t : IsTriple B G X om om') : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.ν 0 := fun x => by
  have h := resEtaPow_div t.chars.resα t.chars.resβ x
  rw [(add_comm a a' ▸ t.geo.even : Even (a' + a)).neg_one_pow] at h
  rw [pow_zero]
  exact h

theorem coneIntegralFactorisation_of (hA : ActsEx) (hI : IdeleFub) (hKF : KFub) (hV : VacFixX) (hS : VacShift) (hAr : ArchCone) (hF : FinM)
    (hP : PureFac) (hSp : SchSpan) (hId : IdealM) : PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation := by
  obtain ⟨a₁, a₂, b₁, b₂, hId⟩ := hId
  refine ⟨a₁, a₂, ?_⟩
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' c e ei ev he hE K μK μ m hK h1 h2 hm
  by_cases ex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' t t₁ => (ex ⟨X, om, om', om₁, om₁', t, t₁⟩).elim⟩
  obtain ⟨X₀, o, o', o₁, o₁', t₀, t₀₁⟩ := ex
  have hC : Cfg B G.M G₁.M H H' e (shiftA H H') :=
    ⟨t₀.base, ⟨_, _, t₀.geo.hV⟩, ⟨_, _, t₀.geo.hW⟩, ⟨_, _, t₀₁.geo.hV⟩, ⟨_, _, t₀₁.geo.hW⟩, t₀.geo.hM, t₀₁.geo.hM,
      ⟨_, _, c.hH⟩, ⟨_, _, c.hH'⟩, .inl ⟨he, rfl⟩⟩
  obtain ⟨𝔞, h0, hlat, hcnt, hval⟩ := hId F E σ B _ _ _ _ _ _ _ _ H H' _ _ _ _ _ _ _ _ t₀.base t₀.geo.hV t₀.geo.hW c.hH c.hH'
    (by omega) (by omega) (by omega) (by omega) _ _ _ (.inl ⟨rfl, rfl, rfl⟩)
  have hz : 2 ≤ (b + 2 - a') / 2 := by
    have := t₀.geo.eBig
    omega
  obtain ⟨κ, hκ, HG⟩ := gen hA hI hKF hV hS hAr hF hP hSp hC hE hK h1 h2 hm h0 hlat hz
  refine ⟨κ, hκ, fun X om om' om₁ om₁' t _ => ?_⟩
  have := HG _ _ _ _ _ _ _ (pairV t) X.ν X.S₀ X.T (nu_cont t) (by classical exact Finset.subset_union_left)
    (unr_div t.chars.unrα t.chars.unrβ) t.chars.unrβ (unr_div t.chars.unrβ t.chars.unrα)
    fun w hw => ⟨t.chars.ram w hw, hcnt w (t.chars.sub hw)⟩
  rw [hval X.ν (nu_cont t) (nu_res t) fun w hw => unr_div t.chars.unrα t.chars.unrβ w fun h => hw (t.chars.sub h)] at this
  exact this

theorem coneFacB_of (hA : ActsEx) (hI : IdeleFub) (hKF : KFub) (hV : VacFixX) (hS : VacShift) (hAr : ArchCone) (hF : FinM)
    (hP : PureFac) (hSp : SchSpan) (hId : IdealM) : ConeFacB := by
  obtain ⟨a₁, a₂, b₁, b₂, hId⟩ := hId
  refine ⟨b₁, b₂, ?_⟩
  intro F E _ _ _ _ _ σ B a b G G₁ H H' c e ei ev he hE K μK μ m hK h1 h2 hm
  by_cases ex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' t t₁ => (ex ⟨X, om, om', om₁, om₁', t, t₁⟩).elim⟩
  obtain ⟨X₀, o, o', o₁, o₁', t₀, t₀₁⟩ := ex
  have hC : Cfg B G.M' G₁.M' H H' e (shiftB σ H H') :=
    ⟨t₀.base, ⟨_, _, t₀.geo.hV'⟩, ⟨_, _, t₀.geo.hW⟩, ⟨_, _, t₀₁.geo.hV'⟩, ⟨_, _, t₀₁.geo.hW⟩, t₀.geo.hM', t₀₁.geo.hM',
      ⟨_, _, c.hH⟩, ⟨_, _, c.hH'⟩, .inr ⟨he, rfl⟩⟩
  obtain ⟨𝔞, h0, hlat, hcnt, hval⟩ := hId F E σ B _ _ _ _ _ _ _ _ H H' _ _ _ _ _ _ _ _ t₀.base t₀.geo.hV' t₀.geo.hW c.hH c.hH'
    (by omega) (by omega) (by omega) (by omega) _ _ _ (.inr ⟨rfl, rfl, rfl⟩)
  have hz : 2 ≤ (a - (b + 2)) / 2 + 1 := by
    have := t₀.geo.eBig
    omega
  obtain ⟨κ, hκ, HG⟩ := gen hA hI hKF hV hS hAr hF hP hSp hC hE hK h1 h2 hm h0 hlat hz
  refine ⟨κ, hκ, fun X om om' om₁ om₁' t _ => ?_⟩
  have := HG _ _ _ _ _ _ _ (pairV' t) X.ν X.S₀ X.T (nu_cont t) (by classical exact Finset.subset_union_left)
    (unr_div t.chars.unrα t.chars.unrβ) t.chars.unrα (unr_div t.chars.unrα t.chars.unrβ)
    fun w hw => ⟨t.chars.ram w hw, hcnt w (t.chars.sub hw)⟩
  rw [hval X.ν (nu_cont t) (nu_res t) fun w hw => unr_div t.chars.unrα t.chars.unrβ w fun h => hw (t.chars.sub h)] at this
  exact this

theorem coneFactorisation_of_codimension_two (h : PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation) : ConeFacA := by
  obtain ⟨e₁, e₂, h⟩ := h
  exact ⟨e₁, e₂, fun F E _ _ _ _ _ σ B b a' G G₁ H H' c => h F E σ B b a' G G₁ H H' ⟨c.eV, c.q1.trans c.q0.symm, c.ep, c.hH, c.hH'⟩⟩

end PositivityTheory.ThKG.Loc.Cone

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Fin

open scoped TensorProduct NNReal Matrix nonZeroDivisors GlobalTheory.VacAny Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac
open GlobalTheory.Doubling (absE)

namespace Sp

section

variable (F : Type) [Field F] [NumberField F] (κ : Type)

def scaledInt (a : F) : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {z | ∀ i (v : HeightOneSpectrum (𝓞 F)),
    (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v ∈ v.adicCompletionIntegers F}
  zero_mem' := fun i v => by
    show (algebraMap F (v.adicCompletion F) a)⁻¹ * (0 : FiniteAdeleRing (𝓞 F) F) v ∈ _
    simp
  add_mem' := fun {z w} hz hw i v => by
    show (algebraMap F (v.adicCompletion F) a)⁻¹ * ((z i + w i) v) ∈ _
    have e : (z i + w i) v = (z i) v + (w i) v := rfl
    rw [e, mul_add]
    exact add_mem (hz i v) (hw i v)
  neg_mem' := fun {z} hz i v => by
    show (algebraMap F (v.adicCompletion F) a)⁻¹ * ((-z i) v) ∈ _
    have e : (-z i) v = -((z i) v) := rfl
    rw [e, mul_neg]
    exact neg_mem (hz i v)

variable {F κ}

theorem mem_scaledInt {a : F} {z : κ → FiniteAdeleRing (𝓞 F) F} :
    z ∈ scaledInt F κ a ↔ ∀ i (v : HeightOneSpectrum (𝓞 F)),
      (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v ∈ v.adicCompletionIntegers F := Iff.rfl

theorem isOpen_scaledInt [Finite κ] (a : F) : IsOpen (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have hO : IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have e : (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) = ⋂ i, (fun z : κ → FiniteAdeleRing (𝓞 F) F =>
      algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) ⁻¹'
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} := by
    ext z
    simp only [SetLike.mem_coe, mem_scaledInt, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
    refine forall_congr' fun i => forall_congr' fun v => ?_
    have h : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v =
        (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v := by
      have h1 := map_mul (evalV F v) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) (z i)
      rw [AlgHom.commutes, map_inv₀ (algebraMap F (v.adicCompletion F))] at h1
      exact h1
    rw [h]
  rw [e]
  exact isOpen_iInter_of_finite fun i => hO.preimage (continuous_const.mul (continuous_apply i))

end

section

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def cosetBoxV (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) : Set (κ → Fv F v) :=
  {x | ∀ i, (algebraMap F (v.adicCompletion F) a)⁻¹ * (x i - (r i) v) ∈ v.adicCompletionIntegers F}

theorem indicator_cosetBoxV_mem_SB [Finite κ] {a : F} (ha : a ≠ 0) (r : κ → FiniteAdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) :
    Set.indicator (cosetBoxV a r v) (1 : (κ → Fv F v) → ℂ) ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  classical
  have ha0 : algebraMap F (v.adicCompletion F) a ≠ 0 := (map_ne_zero _).2 ha
  let P : Set (κ → Fv F v) := Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))
  let f : (κ → Fv F v) → (κ → Fv F v) := fun x i => (algebraMap F (v.adicCompletion F) a)⁻¹ * (x i - (r i) v)
  let g : (κ → Fv F v) → (κ → Fv F v) := fun z i => algebraMap F (v.adicCompletion F) a * z i + (r i) v
  have hf : Continuous f :=
    continuous_pi fun i => continuous_const.mul ((continuous_apply i).sub continuous_const)
  have hg : Continuous g :=
    continuous_pi fun i => (continuous_const.mul (continuous_apply i)).add continuous_const
  have hS : cosetBoxV a r v = f ⁻¹' P := by
    ext x
    simp only [cosetBoxV, P, f, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq,
      SetLike.mem_coe]
  have hPo : IsOpen P := isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  have hPc : IsCompact P := isCompact_univ_pi fun _ => isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  have hcl : IsClopen (cosetBoxV a r v) := by
    rw [hS]
    exact ⟨hPc.isClosed.preimage hf, hPo.preimage hf⟩
  have hco : IsCompact (cosetBoxV a r v) := by
    refine (hPc.image hg).of_isClosed_subset hcl.isClosed ?_
    intro x hx
    refine ⟨f x, ?_, ?_⟩
    · rw [hS] at hx
      exact hx
    · funext i
      simp only [f, g]
      rw [mul_inv_cancel_left₀ ha0, sub_add_cancel]
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ cosetBoxV a r v
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
      rfl
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)

theorem eventually_cosetBoxV_eq {a : F} (ha : a ≠ 0) (r : κ → FiniteAdeleRing (𝓞 F) F) [Finite κ] :
    ∀ᶠ v in cofinite, cosetBoxV a r v = {x | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
  have h1 : ∀ᶠ v in cofinite, (algebraMap F (FiniteAdeleRing (𝓞 F) F) a) v ∈ v.adicCompletionIntegers F :=
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) a).2
  have h2 : ∀ᶠ v in cofinite, (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) v ∈ v.adicCompletionIntegers F :=
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹).2
  have h3 : ∀ᶠ v in cofinite, ∀ i, (r i) v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (r i).2
  filter_upwards [h1, h2, h3] with v hv1 hv2 hv3
  have ha0 : algebraMap F (v.adicCompletion F) a ≠ 0 := (map_ne_zero _).2 ha
  have e1 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a) v = algebraMap F (v.adicCompletion F) a := rfl
  have e2 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) v = (algebraMap F (v.adicCompletion F) a)⁻¹ := by
    show algebraMap F (v.adicCompletion F) a⁻¹ = _
    exact map_inv₀ _ a
  rw [e1] at hv1
  rw [e2] at hv2
  ext x
  simp only [cosetBoxV, Set.mem_setOf_eq]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h => ?_⟩
  · have hd : x i - (r i) v ∈ v.adicCompletionIntegers F := by
      rw [← mul_inv_cancel_left₀ ha0 (x i - (r i) v)]
      exact mul_mem hv1 h
    have e : x i = (x i - (r i) v) + (r i) v := (sub_add_cancel _ _).symm
    rw [e]
    exact add_mem hd (hv3 i)
  · exact mul_mem hv2 (sub_mem h (hv3 i))

theorem indicator_coset_scaledInt_eq_finprod : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F)
    (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    ∃ φ : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) y =
        ∏ᶠ v, φ v fun i => evalV F v (y i) := by
  intro F _ _ κ _ a r ha
  classical
  refine ⟨fun v => Set.indicator (cosetBoxV a r v) 1, fun v => indicator_cosetBoxV_mem_SB ha r v, ?_, ?_⟩
  · filter_upwards [eventually_cosetBoxV_eq ha r] with v hv
    rw [hv]
  · intro y
    have hmem : ∀ v, (fun i => evalV F v (y i)) ∈ cosetBoxV a r v ↔
        ∀ i, (algebraMap F (v.adicCompletion F) a)⁻¹ * ((y - r) i) v ∈ v.adicCompletionIntegers F :=
      fun v => Iff.rfl
    by_cases hy : y - r ∈ scaledInt F κ a
    · rw [Set.indicator_of_mem (show y ∈ {y | y - r ∈ scaledInt F κ a} from hy)]
      have h1 : ∀ v, Set.indicator (cosetBoxV a r v) (1 : (κ → Fv F v) → ℂ) (fun i => evalV F v (y i)) = 1 :=
        fun v => by rw [Set.indicator_of_mem ((hmem v).2 fun i => hy i v)]; rfl
      rw [finprod_congr h1, finprod_one]
    · rw [Set.indicator_of_notMem (show y ∉ {y | y - r ∈ scaledInt F κ a} from hy)]
      rw [mem_scaledInt] at hy
      push_neg at hy
      obtain ⟨i, v, hv⟩ := hy
      symm
      refine finprod_eq_zero _ v ?_ ?_
      · exact Set.indicator_of_notMem (fun h => hv ((hmem v).1 h i)) _
      · have hint : ∀ᶠ w in cofinite, ∀ i, evalV F w (y i) ∈ w.adicCompletionIntegers F :=
          Filter.eventually_all.2 fun i => (y i).2
        refine (Filter.eventually_cofinite.1 ((eventually_cosetBoxV_eq ha r).and hint)).subset ?_
        intro w hw h'
        apply hw
        simp only [Function.mem_mulSupport, not_not]
        rw [h'.1, Set.indicator_of_mem (show (fun i => evalV F w (y i)) ∈ {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from h'.2)]
        rfl

end

theorem exists_scaled_integral_lattice_subset : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (W : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    W ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) → ∃ a : F, a ≠ 0 ∧ (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ W := by
  intro F _ _ κ _ W hW
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hsub⟩ := hW
  obtain ⟨M, hM, hlev⟩ := GlobalTheory.IdeleCharLevel.exists_level F (⋂ i, t i) (Filter.iInter_mem.2 ht)
  refine ⟨M, Nat.cast_ne_zero.2 hM, fun z hz => hsub fun i _ => Set.mem_iInter.1 (hlev (z i) fun v => ?_) i⟩
  have h0 : v.intValuation (M : 𝓞 F) ≠ 0 := v.intValuation_ne_zero _ (Nat.cast_ne_zero.2 hM)
  have e1 : Valued.v (algebraMap F (v.adicCompletion F) (M : F)) = v.intValuation (M : 𝓞 F) := by
    rw [← map_natCast (algebraMap (𝓞 F) F), ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have h := mem_scaledInt.1 hz i v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, e1, inv_mul_le_iff₀ (zero_lt_iff.mpr h0), mul_one] at h
  exact h

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_invariant {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∀ x, ∀ z ∈ scaledInt F κ a, g (x + z) = g x := by
  obtain ⟨hlc, hcs⟩ := hg
  have hW : ∀ y, {z | g (y + z) = g y} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) := fun y =>
    ((hlc.isOpen_fiber (g y)).preimage (continuous_const.add continuous_id)).mem_nhds (by simp)
  choose b hb hbW using fun y => exists_scaled_integral_lattice_subset F κ _ (hW y)
  have hN : ∀ y ∈ tsupport g, {x | x - y ∈ scaledInt F κ (b y)} ∈ 𝓝 y := fun y _ =>
    ((isOpen_scaledInt (b y)).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hcs _ hN
  have hW0 : (⋂ y ∈ t, (scaledInt F κ (b y) : Set (κ → FiniteAdeleRing (𝓞 F) F))) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
    (Filter.biInter_finset_mem t).2 fun y _ => (isOpen_scaledInt (b y)).mem_nhds (zero_mem _)
  obtain ⟨a, ha, haW⟩ := exists_scaled_integral_lattice_subset F κ _ hW0
  refine ⟨a, ha, fun x z hz => ?_⟩
  have key : ∀ y ∈ t, x - y ∈ scaledInt F κ (b y) → g (x + z) = g x := fun y hy hxy => by
    have hz' : z ∈ scaledInt F κ (b y) := Set.mem_iInter₂.1 (haW hz) y hy
    have h1 : g (y + (x - y)) = g y := hbW y hxy
    have h2 : g (y + (x - y + z)) = g y := hbW y (add_mem hxy hz')
    rw [add_sub_cancel] at h1
    rw [show y + (x - y + z) = x + z by abel] at h2
    rw [h1, h2]
  by_cases hx : x ∈ tsupport g
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact key y hy hxy
  by_cases hxz : x + z ∈ tsupport g
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hxz)
    have hz' : z ∈ scaledInt F κ (b y) := Set.mem_iInter₂.1 (haW hz) y hy
    refine key y hy ?_
    have := sub_mem hxy hz'
    rwa [show x + z - y - z = x - y by abel] at this
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxz]

theorem exists_sum_cosets {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
      g = ∑ r ∈ R, g r • Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) := by
  obtain ⟨a, ha, hinv⟩ := exists_invariant hg
  refine ⟨a, ha, ?_⟩
  set U := scaledInt F κ a
  have hN : ∀ y ∈ tsupport g, {x | x - y ∈ U} ∈ 𝓝 y := fun y _ =>
    ((isOpen_scaledInt a).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hg.2 _ hN
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ tsupport g, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  refine ⟨R, funext fun x => ?_⟩
  rw [Finset.sum_apply]
  by_cases hx : ∃ r ∈ R, x - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · have h := hinv r0 (x - r0) hxr0
      rw [add_sub_cancel] at h
      simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem (show x ∈ {y | y - r0 ∈ U} from hxr0), mul_one, h]
    · intro r hr hne
      have hm : x ∉ {y | y - r ∈ U} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hm, mul_zero]
  · push Not at hx
    have hK : x ∉ tsupport g := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [image_eq_zero_of_notMem_tsupport hK]
    symm
    refine Finset.sum_eq_zero fun r hr => ?_
    have hm : x ∉ {y | y - r ∈ U} := hx r hr
    simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hm, mul_zero]

theorem exists_sum_finprod {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (φ : Fin m → ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ),
      (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ k, ∀ᶠ v in cofinite, φ k v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      g = ∑ k, c k • fun y => ∏ᶠ v, φ k v fun i => evalV F v (y i) := by
  obtain ⟨a, ha, R, hR⟩ := exists_sum_cosets hg
  choose φ hSB hstd hφ using fun r : κ → FiniteAdeleRing (𝓞 F) F => indicator_coset_scaledInt_eq_finprod F κ a r ha
  let e := R.equivFin
  refine ⟨R.card, fun k => g (e.symm k), fun k => φ (e.symm k), fun k v => hSB _ v, fun k => hstd _, ?_⟩
  have hind : ∀ r, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) =
      fun y => ∏ᶠ v, φ r v fun i => evalV F v (y i) := fun r => funext (hφ r)
  refine hR.trans ?_
  simp only [hind]
  rw [← Finset.sum_coe_sort R]
  exact (Equiv.sum_comp e.symm (fun x : R => g x • fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ x v fun i => evalV F v (y i))).symm

end Sp

theorem schSpan : SchSpan := by
  intro F _ _ κ _ vac hSB hstd
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    obtain ⟨m, c, φ, h1, h2, rfl⟩ := Sp.exists_sum_finprod hg
    have e : pureA F f (∑ k, c k • fun y => ∏ᶠ v, φ k v fun i => evalV F v (y i)) = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
      funext x
      simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
      exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _
    rw [e]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    have hf : {v | ¬ φ k v = vac v}.Finite := by
      refine eventually_cofinite.1 ?_
      filter_upwards [h2 k, hstd] with v a b using a.trans b.symm
    exact ⟨f, φ k, hf.toFinset, h1 k, fun v hv => by simpa using hv, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, φ, T, h1, h2, rfl⟩
    refine GlobalTheory.TensUniq.pure_mem_schA f φ h1 ?_
    filter_upwards [T.eventually_cofinite_notMem, hstd] with v a b using (h2 v a).trans b

end PositivityTheory.ThKG.Loc.Cone.Fin

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Id

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes WithZero
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Idele
open Formalism.L2.Host (IsUnitAt IsUnifAt atFin unif unif_spec)
open FractionalIdeal (count)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev FI (E : Type) [Field E] [NumberField E] : Type := FractionalIdeal (𝓞 E)⁰ E

variable (F) in

def cp (w : HeightOneSpectrum (𝓞 E)) : AE F E →+* w.adicCompletion E :=
  (evalV E w).toRingHom.comp ((finAdEquiv F E).toRingHom.comp (finTens F E))

theorem cp_apply (w : HeightOneSpectrum (𝓞 E)) (x : AE F E) : cp F w x = finAdEquiv F E (finTens F E x) w := rfl

theorem inAt_iff {𝔞 : FI E} {v : Pl F} {x : AE F E} :
    InAt 𝔞 v x ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → Valued.v (cp F w x) ≤ exp (-count E w 𝔞) := Iff.rfl

theorem cp_tmul (w : HeightOneSpectrum (𝓞 E)) (a : AF F) (s : E) :
    cp F w (a ⊗ₜ[F] s) = complMap rfl (evFin F (w.under (𝓞 F)) a) * algebraMap E _ s := rfl

theorem smul_eq (a : AF F) (x : AE F E) : a • x = (a ⊗ₜ[F] (1 : E)) * x := Algebra.smul_def a x

theorem cp_smul (w : HeightOneSpectrum (𝓞 E)) (a : AF F) (x : AE F E) :
    cp F w (a • x) = complMap rfl (evFin F (w.under (𝓞 F)) a) * cp F w x := by
  rw [smul_eq, map_mul, cp_tmul, map_one, mul_one]

theorem ev_idem (v : Pl F) : evFin F v (idem F v) = 1 := evalV_singleFin_self v 1

theorem ev_idem_ne {v u : Pl F} (h : u ≠ v) : evFin F u (idem F v) = 0 := evalV_singleFin_ne h 1

theorem at_idem (v : Pl F) : At (evFin F v) (idem F v) := GlobalTheory.LatVac.at_liftV v 1

theorem cp_idem {w : HeightOneSpectrum (𝓞 E)} {v : Pl F} (h : w.under (𝓞 F) = v) (x : AE F E) :
    cp F w (idem F v • x) = cp F w x := by
  subst h; rw [cp_smul, ev_idem, map_one, one_mul]

theorem cp_idem_ne {w : HeightOneSpectrum (𝓞 E)} {v : Pl F} (h : w.under (𝓞 F) ≠ v) (x : AE F E) :
    cp F w (idem F v • x) = 0 := by
  rw [cp_smul, ev_idem_ne h, map_zero, zero_mul]

theorem inf_idem (v : Pl F) (x : AE F E) : infTens F E (idem F v • x) = 0 := by
  rw [smul_eq, map_mul]
  have : infTens F E (idem F v ⊗ₜ[F] (1 : E)) = 0 := TensorProduct.zero_tmul _ _
  rw [this, zero_mul]

theorem ext_cp {x y : AE F E} (h1 : infTens F E x = infTens F E y) (h2 : ∀ w, cp F w x = cp F w y) : x = y :=
  tens_ext h1 ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ h2))

def Lat (𝔞 : FI E) (v : Pl F) : AddSubgroup (AE F E) :=
  AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ s ∈ 𝔞, z = a ⊗ₜ[F] s}

theorem inAt_of_lat {𝔞 : FI E} (h0 : 𝔞 ≠ 0) {v : Pl F} {z : AE F E} (hz : z ∈ Lat 𝔞 v) : InAt 𝔞 v z := by
  rw [inAt_iff]
  intro w hw
  subst hw
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, s, hs, rfl⟩ := hz
    rw [cp_tmul, map_mul, valued_algebraMap]
    have h1 : Valued.v (complMap (rfl : w.under (𝓞 F) = _) (evFin F _ a)) ≤ 1 := complMap_mem rfl ha
    exact (mul_le_of_le_one_left' h1).trans ((mem_iff_valuation_le h0 s).1 hs w)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [map_neg, Valuation.map_neg]

theorem lat_of_inAt {𝔞 : FI E} (h0 : 𝔞 ≠ 0) {v : Pl F} {x : AE F E} (hx : InAt 𝔞 v x) : idem F v • x ∈ Lat 𝔞 v := by
  have h1 : (1 : E) ∈ 𝔞 * 𝔞⁻¹ := by rw [mul_inv_cancel₀ h0]; exact FractionalIdeal.one_mem_one _
  have key : idem F v • (((1 : AF F) ⊗ₜ[F] (1 : E)) * x) ∈ Lat 𝔞 v := by
    refine FractionalIdeal.mul_induction_on (C := fun r => idem F v • (((1 : AF F) ⊗ₜ[F] r) * x) ∈ Lat 𝔞 v) h1 ?_ ?_
    · intro s hs t ht
      set y := idem F v • (((1 : AF F) ⊗ₜ[F] t) * x) with hy
      have hint := (mem_int_iff (finTens F E y)).2 fun P => by
        rw [← cp_apply]
        by_cases hP : P.under (𝓞 F) = v
        · rw [hy, cp_idem hP, map_mul, cp_tmul, map_one, map_one, one_mul, map_mul, valued_algebraMap]
          have a1 := (mem_iff_valuation_le (inv_ne_zero h0) t).1 ht P
          rw [FractionalIdeal.count_inv, neg_neg] at a1
          refine (mul_le_mul' a1 (inAt_iff.1 hx P hP)).trans ?_
          rw [← exp_add]; simp
        · rw [hy, cp_idem_ne hP]; simp
      have e1 : extZero F E (finTens F E y) = y :=
        tens_ext (by rw [infTens_extZero, hy, inf_idem]) (finTens_extZero _)
      have h2 : ∀ y' ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)},
          idem F v • (((1 : AF F) ⊗ₜ[F] s) * extZero F E y') ∈ Lat 𝔞 v := fun y' hy' => by
        induction hy' using AddSubgroup.closure_induction with
        | mem z hz =>
          obtain ⟨a, ha, o, rfl⟩ := hz
          refine AddSubgroup.subset_closure ⟨idem F v * pairA F 0 a,
            GlobalTheory.VacAny.at_mul_right (at_idem v) _, ?_, s * o, ?_, ?_⟩
          · rw [map_mul, ev_idem, one_mul]; exact ha v
          · rw [mul_comm]; exact 𝔞.val.smul_mem o hs
          · change idem F v • (((1 : AF F) ⊗ₜ[F] s) * (pairA F 0 a ⊗ₜ[F] (o : E))) = _
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', smul_eq_mul]
        | zero => rw [map_zero, mul_zero, smul_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [map_add, mul_add, smul_add]; exact add_mem hx hy
        | neg x _ hx => rw [map_neg, mul_neg, smul_neg]; exact neg_mem hx
      have h3 := h2 _ hint
      rw [e1, hy, mul_smul_comm, smul_smul, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at h3
      have hi : idem F v * idem F v = idem F v := (GlobalTheory.LatVacArith.eq_liftV_of_at (at_idem v)).symm
      rwa [hi] at h3
    · intro a b ha hb
      rw [TensorProduct.tmul_add, add_mul, smul_add]; exact add_mem ha hb
  rwa [show ((1 : AF F) ⊗ₜ[F] (1 : E)) = 1 from rfl, one_mul] at key

theorem lat_iff {𝔞 : FI E} (h0 : 𝔞 ≠ 0) {v : Pl F} {x : AE F E} : idem F v • x ∈ Lat 𝔞 v ↔ InAt 𝔞 v x :=
  ⟨fun h => inAt_iff.2 fun w hw => cp_idem hw x ▸ inAt_iff.1 (inAt_of_lat h0 h) w hw, lat_of_inAt h0⟩

def so (σ : E →ₐ[F] E) (o : 𝓞 E) : 𝓞 E := ⟨σ o, (RingOfIntegers.isIntegral_coe o).map (σ.restrictScalars ℤ)⟩

def cj (hσ : ∀ x, σ (σ x) = x) (𝔞 : FI E) : FI E :=
  ⟨{ carrier := {t | σ t ∈ 𝔞}
     add_mem' := fun {a b} ha hb => by
       change σ (a + b) ∈ 𝔞
       rw [map_add]; exact 𝔞.val.add_mem ha hb
     zero_mem' := by
       change σ 0 ∈ 𝔞
       rw [map_zero]; exact 𝔞.zero_mem
     smul_mem' := fun c x hx => by
       change σ ((c : E) * x) ∈ 𝔞
       rw [map_mul]; exact 𝔞.val.smul_mem (so σ c) hx }, by
    obtain ⟨a, ha, h⟩ := 𝔞.isFractional
    refine ⟨so σ a, mem_nonZeroDivisors_of_ne_zero fun e => nonZeroDivisors.ne_zero ha ?_, fun b hb => ?_⟩
    · have : σ (a : E) = 0 := congrArg Subtype.val e
      exact Subtype.ext ((map_eq_zero σ).1 this)
    · obtain ⟨c, hc⟩ := h _ hb
      refine ⟨so σ c, ?_⟩
      change σ (algebraMap _ E c) = σ a * b
      rw [hc]
      change σ ((a : E) * σ b) = _
      rw [map_mul, hσ]⟩

variable (hσ : ∀ x, σ (σ x) = x)

theorem mem_cj {𝔞 : FI E} {t : E} : t ∈ cj hσ 𝔞 ↔ σ t ∈ 𝔞 := Iff.rfl

theorem cj_cj (𝔞 : FI E) : cj hσ (cj hσ 𝔞) = 𝔞 := FractionalIdeal.ext fun x => by rw [mem_cj, mem_cj, hσ]

theorem cj_ne {𝔞 : FI E} (h : 𝔞 ≠ 0) : cj hσ 𝔞 ≠ 0 := fun e => h (FractionalIdeal.eq_zero_iff.2 fun x hx => by
  have : σ x ∈ cj hσ 𝔞 := (mem_cj hσ).2 (by rwa [hσ])
  rw [e, FractionalIdeal.mem_zero_iff] at this
  exact (map_eq_zero σ).1 this)

theorem mem_one_conj {x : E} (h : x ∈ (1 : FI E)) : σ x ∈ (1 : FI E) := by
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact (FractionalIdeal.mem_one_iff _).2 ⟨so σ o, rfl⟩

theorem cj_inv {𝔞 : FI E} (h : 𝔞 ≠ 0) : cj hσ 𝔞⁻¹ = (cj hσ 𝔞)⁻¹ := FractionalIdeal.ext fun x => by
  rw [mem_cj, FractionalIdeal.mem_inv_iff h, FractionalIdeal.mem_inv_iff (cj_ne hσ h)]
  constructor
  · intro H y hy
    have := mem_one_conj (σ := σ) (H _ hy)
    rwa [map_mul, hσ, hσ] at this
  · intro H y hy
    have := mem_one_conj (σ := σ) (H (σ y) ((mem_cj hσ).2 (by rwa [hσ])))
    rwa [map_mul, hσ] at this

theorem lat_cj {𝔞 : FI E} {v : Pl F} {z : AE F E} (hz : z ∈ Lat 𝔞 v) : cA σ z ∈ Lat (cj hσ 𝔞) v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, h1, h2, s, hs, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a, h1, h2, σ s, (mem_cj hσ).2 (by rwa [hσ]), rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem inAt_cj {𝔞 : FI E} (h0 : 𝔞 ≠ 0) {v : Pl F} {x : AE F E} (h : InAt 𝔞 v x) : InAt (cj hσ 𝔞) v (cA σ x) := by
  have := lat_cj hσ (lat_of_inAt h0 h)
  rw [map_smul] at this
  exact (lat_iff (cj_ne hσ h0)).1 this

theorem inAt_cj_iff {𝔞 : FI E} (h0 : 𝔞 ≠ 0) {v : Pl F} {x : AE F E} : InAt 𝔞 v (cA σ x) ↔ InAt (cj hσ 𝔞) v x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := inAt_cj hσ h0 h
    rwa [PositivityTheory.ThK.Vac.cA_cA hσ] at this
  · have := inAt_cj hσ (cj_ne hσ h0) h
    rwa [cj_cj] at this

theorem cp_loc_self (w : HeightOneSpectrum (𝓞 E)) (y : (w.adicCompletion E)ˣ) : cp F w (locIdele F w y : AE F E) = y := by
  rw [cp_apply, finTens_locIdele]; exact finSingle_self w _

theorem cp_loc_ne {w u : HeightOneSpectrum (𝓞 E)} (h : u ≠ w) (y : (w.adicCompletion E)ˣ) :
    cp F u (locIdele F w y : AE F E) = 1 := by
  rw [cp_apply, finTens_locIdele]; exact finSingle_ne h _

theorem cp_prod (S : Finset (HeightOneSpectrum (𝓞 E))) (y : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (u : HeightOneSpectrum (𝓞 E)) : cp F u ((∏ w ∈ S, locIdele F w (y w) : (AE F E)ˣ) : AE F E) = by
      classical exact if u ∈ S then (y u : u.adicCompletion E) else 1 := by
  classical
  rw [Units.coe_prod, map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem u h fun w _ hw => cp_loc_ne hw.symm _, cp_loc_self]
  · exact Finset.prod_eq_one fun w hw => cp_loc_ne (fun e : u = w => h (e ▸ hw)) _

theorem inf_prod (S : Finset (HeightOneSpectrum (𝓞 E))) (y : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) :
    infTens F E ((∏ w ∈ S, locIdele F w (y w) : (AE F E)ˣ) : AE F E) = 1 := by
  rw [Units.coe_prod, map_prod]; exact Finset.prod_eq_one fun w _ => infTens_locIdele w _

theorem locChar_eq {ν : Chr F E} {w : HeightOneSpectrum (𝓞 E)} (h : UnrAt ν w) (x : (w.adicCompletion E)ˣ) {k : ℤ}
    (hx : Valued.v (x : w.adicCompletion E) = exp (-k)) : locChar ν w x = val ν w ^ k := by
  have h1 : IsUnitAt w (x * (atFin w (unif w) ^ k)⁻¹) := by
    have := unif_spec w
    unfold IsUnifAt at this
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, hx, this,
      ← exp_zsmul, smul_eq_mul, mul_neg, mul_one, mul_inv_cancel₀ exp_ne_zero]
  have := h _ h1
  rw [map_mul, map_inv, mul_inv_eq_one, map_zpow] at this
  exact this

structure Gen (P : Finset (Pl F)) (𝔞 : FI E) (T : Finset (Pl F)) (l : (AE F E)ˣ) : Prop where
  dis : ∀ v ∈ T, v ∉ P
  inf : infTens F E l = 1
  off : ∀ v ∉ T, idem F v • (l : AE F E) = idem F v • (1 : AE F E)
  vl : ∀ w, Valued.v (cp F w l) = exp (-count E w 𝔞)

theorem Gen.eq {P T : Finset (Pl F)} {𝔞 : FI E} {l : (AE F E)ˣ} (h : Gen P 𝔞 T l) {ν : Chr F E}
    (hν : UnrOff ν (P : Set (Pl F))) : Circle.toUnits (ν l) = idealVal ν 𝔞 := by
  classical
  let S := T.biUnion fun v => Formalism.L2.Host.aboveF (L := E) F v
  have hS : ∀ w, w ∈ S ↔ w.under (𝓞 F) ∈ T := fun w => by simp [S, mem_aboveF]
  have h1 : ∀ w ∉ S, cp F w l = 1 := fun w hw => by
    have := congrArg (cp F w) (h.off _ (mt (hS w).2 hw))
    rwa [cp_idem rfl, cp_idem rfl, map_one] at this
  have e : l = ∏ w ∈ S, locIdele F w (Units.map (cp F w).toMonoidHom l) :=
    Units.ext (ext_cp (h.inf.trans (inf_prod _ _).symm) fun w => by
      rw [cp_prod]; split_ifs with hw
      exacts [rfl, h1 w hw])
  have h2 : ∀ w ∉ S, count E w 𝔞 = 0 := fun w hw => by
    have := h.vl w
    rw [h1 w hw, map_one, ← exp_zero, exp_inj] at this
    omega
  rw [idealVal, finprod_eq_prod_of_mulSupport_subset (s := S) _ fun w hw => by
    by_contra hn; exact hw (by simp [h2 w hn])]
  conv_lhs => rw [e]
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun w hw =>
    locChar_eq (hν w fun hP => h.dis _ ((hS w).1 hw) hP) _ (h.vl w)

def Pr (P : Finset (Pl F)) (𝔞 : FI E) : Prop := ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ P → count E w 𝔞 = 0

theorem exists_gen {P : Finset (Pl F)} {𝔞 : FI E} (h : Pr P 𝔞) : ∃ T l, Gen P 𝔞 T l := by
  classical
  have hf : {w : HeightOneSpectrum (𝓞 E) | count E w 𝔞 ≠ 0}.Finite := FractionalIdeal.finite_factors 𝔞
  refine ⟨hf.toFinset.image fun w => w.under (𝓞 F), ∏ w ∈ hf.toFinset, locIdele F w (atFin w (unif w) ^ count E w 𝔞),
    fun v hv hP => ?_, inf_prod _ _, fun v hv => ext_cp (by rw [inf_idem, inf_idem]) fun w => ?_, fun w => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    exact hf.mem_toFinset.1 hw (h w hP)
  · by_cases hw : w.under (𝓞 F) = v
    · rw [cp_idem hw, cp_idem hw, cp_prod, if_neg fun hm => hv (Finset.mem_image.2 ⟨w, hm, hw⟩), map_one]
    · rw [cp_idem_ne hw, cp_idem_ne hw]
  · rw [cp_prod]
    split_ifs with hw
    · have := unif_spec w
      unfold IsUnifAt at this
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, this, ← exp_zsmul, smul_eq_mul, mul_neg, mul_one]
    · have : count E w 𝔞 = 0 := by by_contra hn; exact hw (hf.mem_toFinset.2 hn)
      simp [this]

theorem vl_of_inAt {𝔞 : FI E} {l : (AE F E)ˣ} {w : HeightOneSpectrum (𝓞 E)} (h1 : InAt 𝔞 (w.under (𝓞 F)) (l : AE F E))
    (h2 : InAt 𝔞⁻¹ (w.under (𝓞 F)) ((l⁻¹ : (AE F E)ˣ) : AE F E)) : Valued.v (cp F w l) = exp (-count E w 𝔞) := by
  have a1 := inAt_iff.1 h1 w rfl
  have a2 := inAt_iff.1 h2 w rfl
  rw [FractionalIdeal.count_inv, neg_neg] at a2
  have a3 : Valued.v (cp F w l) * Valued.v (cp F w ((l⁻¹ : (AE F E)ˣ) : AE F E)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc exp (-count E w 𝔞) = exp (-count E w 𝔞) * (Valued.v (cp F w l) * Valued.v (cp F w ((l⁻¹ : (AE F E)ˣ) : AE F E))) := by
        rw [a3, mul_one]
    _ ≤ exp (-count E w 𝔞) * (Valued.v (cp F w l) * exp (count E w 𝔞)) := by gcongr
    _ = _ := by rw [mul_left_comm, ← exp_add]; simp

theorem Gen.conj {P T : Finset (Pl F)} {𝔞 : FI E} (h0 : 𝔞 ≠ 0) {l : (AE F E)ˣ} (h : Gen P 𝔞 T l) :
    Gen P (cj hσ 𝔞) T (Units.map (cA σ : AE F E →* AE F E) l) := by
  refine ⟨h.dis, ?_, fun v hv => ?_, fun w => vl_of_inAt ?_ ?_⟩
  · have : ∀ x : AE F E, infTens F E (cA σ x) = Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ (infTens F E x) := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a e => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    change infTens F E (cA σ l) = 1
    rw [this, h.inf, map_one]
  · have := congrArg (cA σ) (h.off v hv)
    rwa [map_smul, map_smul, map_one] at this
  · exact inAt_cj hσ h0 (inAt_iff.2 fun u _ => (h.vl u).le)
  · rw [← cj_inv hσ h0]
    refine inAt_cj hσ (inv_ne_zero h0) (x := ((l⁻¹ : (AE F E)ˣ) : AE F E)) (inAt_iff.2 fun u _ => le_of_eq ?_)
    have a3 : Valued.v (cp F u l) * Valued.v (cp F u ((l⁻¹ : (AE F E)ˣ) : AE F E)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    rw [h.vl] at a3
    rw [FractionalIdeal.count_inv, neg_neg, eq_inv_of_mul_eq_one_right a3, ← exp_neg, neg_neg]

theorem idealVal_mul (ν : Chr F E) {𝔞 𝔟 : FI E} (ha : 𝔞 ≠ 0) (hb : 𝔟 ≠ 0) :
    idealVal ν (𝔞 * 𝔟) = idealVal ν 𝔞 * idealVal ν 𝔟 := by
  have hf : ∀ 𝔠 : FI E, (Function.mulSupport fun w => val ν w ^ count E w 𝔠).Finite := fun 𝔠 =>
    Set.Finite.subset (FractionalIdeal.finite_factors 𝔠) fun w hw hc => hw (by simp [show count E w 𝔠 = 0 from hc])
  unfold idealVal
  rw [← finprod_mul_distrib (hf 𝔞) (hf 𝔟)]
  exact finprod_congr fun w => by rw [FractionalIdeal.count_mul _ _ ha hb, zpow_add]

theorem idealVal_inv (ν : Chr F E) (𝔞 : FI E) : idealVal ν 𝔞⁻¹ = (idealVal ν 𝔞)⁻¹ := by
  unfold idealVal
  rw [← finprod_inv_distrib]
  exact finprod_congr fun w => by rw [FractionalIdeal.count_inv, zpow_neg]

theorem idealVal_cj {P : Finset (Pl F)} {𝔞 : FI E} (h0 : 𝔞 ≠ 0) (h : Pr P 𝔞) {ν : Chr F E} (hν : UnrOff ν (P : Set (Pl F)))
    (hc : ∀ z, ν (Units.map (cA σ : AE F E →* AE F E) z) = (ν z)⁻¹) : idealVal ν (cj hσ 𝔞) = (idealVal ν 𝔞)⁻¹ := by
  obtain ⟨T, l, hl⟩ := exists_gen h
  rw [← (hl.conj hσ h0).eq hν, ← hl.eq hν, hc, map_inv]

end PositivityTheory.ThKG.Loc.Cone.Id

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Id

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes WithZero
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Idele
open Formalism.L2.Host (IsUnitAt IsUnifAt atFin unif unif_spec)
open FractionalIdeal (count)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem add_sigma (h : IsCMExt F E σ) (x : E) : x + σ x = algebraMap F E (Algebra.trace F E x) := by
  classical
  have hc := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (by ext y; simp [PositivityTheory.ThK.Vac.sigma_sigma h]) (by ext y; simp [PositivityTheory.ThK.Vac.sigma_sigma h])
  have hs : (1 : E ≃ₐ[F] E) ≠ s := by
    intro h1
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext y
    have h2 : σ y = y := (DFunLike.congr_fun h1 y).symm
    have := h.2.2.2 τ y
    rw [h2] at this
    simpa using this.symm
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hs, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h.2.2.1]
  rw [trace_eq_sum_automorphisms, hu, Finset.sum_pair hs]
  rfl

theorem add_cA (h : IsCMExt F E σ) (z : AE F E) : ∃ a : AF F, z + cA σ z = algebraMap (AF F) (AE F E) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ← ha, ← hb]; ring⟩
  | tmul a e =>
    refine ⟨Algebra.trace F E e • a, ?_⟩
    change a ⊗ₜ[F] e + a ⊗ₜ[F] σ e = (Algebra.trace F E e • a) ⊗ₜ[F] (1 : E)
    rw [← TensorProduct.tmul_add, add_sigma h, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem fixed_cA (h : IsCMExt F E σ) {z : AE F E} (hz : cA σ z = z) : ∃ a : AF F, z = algebraMap (AF F) (AE F E) a := by
  obtain ⟨a, ha⟩ := add_cA h z
  refine ⟨⅟(2 : AF F) * a, ?_⟩
  rw [map_mul, ← ha, hz, ← two_mul, ← mul_assoc, ← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self,
    map_one, one_mul]

theorem nu_conj (h : IsCMExt F E σ) {ν : Chr F E} (hν : ∀ a : (AF F)ˣ, ν (ideleMap F E a) = 1) (z : (AE F E)ˣ) :
    ν (Units.map (cA σ : AE F E →* AE F E) z) = (ν z)⁻¹ := by
  have hσ := PositivityTheory.ThK.Vac.cA_cA (F := F) (PositivityTheory.ThK.Vac.sigma_sigma h)
  set y := z * Units.map (cA σ : AE F E →* AE F E) z with hy
  have f : ∀ u : (AE F E)ˣ, cA σ ((u * Units.map (cA σ : AE F E →* AE F E) u : (AE F E)ˣ) : AE F E) =
      (u * Units.map (cA σ : AE F E →* AE F E) u : (AE F E)ˣ) := fun u => by
    change cA σ (u * cA σ u) = u * cA σ u
    rw [map_mul, hσ, mul_comm]
  obtain ⟨a, ha⟩ := fixed_cA h (f z)
  obtain ⟨b, hb⟩ := fixed_cA h (f z⁻¹)
  have hab : a * b = 1 := by
    apply Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := AF F) (B := E) (algebraMap F E).injective
    change algebraMap (AF F) (AE F E) (a * b) = algebraMap (AF F) (AE F E) 1
    rw [map_mul, ← ha, ← hb, map_one, ← Units.val_mul, map_inv, ← mul_inv, mul_inv_cancel, Units.val_one]
  have : y = ideleMap F E ⟨a, b, hab, (mul_comm b a).trans hab⟩ := Units.ext ha
  have h2 := hν ⟨a, b, hab, (mul_comm b a).trans hab⟩
  rw [← this, hy, map_mul] at h2
  exact eq_inv_of_mul_eq_one_right h2

theorem inD_iff (z : E) : (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * z))) ↔ z ∈ codiff E := by
  rw [FractionalIdeal.mem_dual (one_ne_zero (α := FI E))]
  constructor
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨q, hq⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 (h o)
    refine ⟨q, ?_⟩
    rw [hq, Algebra.traceForm_apply, mul_comm]
  · intro h o
    obtain ⟨q, hq⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply] at hq
    rw [mul_comm]
    have : Algebra.trace ℚ E (z * (o : E)) = algebraMap ℤ ℚ q := by rw [hq]
    rw [this]; exact isIntegral_algebraMap

theorem exp_count_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] {I : FI K} {J : FI L} (hI : I ≠ 0) (hJ : J ≠ 0)
    (f : K →+* L) (h1 : ∀ t ∈ I, f t ∈ J) (h2 : ∀ t ∈ I⁻¹, f t ∈ J⁻¹) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hm : ∀ s t, v.valuation K s = v.valuation K t → w.valuation L (f s) = w.valuation L (f t)) {x : K}
    (hx : v.valuation K x = exp (-count K v I)) : w.valuation L (f x) = exp (-count L w J) := by
  obtain ⟨s, hs, es⟩ := exists_mem_valuation_eq hI v
  obtain ⟨t, ht, et⟩ := exists_mem_valuation_eq (inv_ne_zero hI) v
  have a1 := (mem_iff_valuation_le hJ _).1 (h1 s hs) w
  have a2 := (mem_iff_valuation_le (inv_ne_zero hJ) _).1 (h2 t ht) w
  rw [FractionalIdeal.count_inv, neg_neg] at a2 et
  have a3 : w.valuation L (f s) * w.valuation L (f t) = 1 := by
    rw [← map_mul, ← map_mul, hm (s * t) 1 (by rw [map_mul, es, et, ← exp_add, map_one]; simp), map_one, map_one]
  rw [hm x s (hx.trans es.symm)]
  refine le_antisymm a1 ?_
  calc exp (-count L w J) = exp (-count L w J) * (w.valuation L (f s) * w.valuation L (f t)) := by rw [a3, mul_one]
    _ ≤ exp (-count L w J) * (w.valuation L (f s) * exp (count L w J)) := by gcongr
    _ = _ := by rw [mul_left_comm, ← exp_add]; simp

theorem codiff_up (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) {w : HeightOneSpectrum (𝓞 E)} {x : F}
    (hx : (w.under (𝓞 F)).valuation F x = exp (-count F (w.under (𝓞 F)) (codiff F))) :
    w.valuation E (algebraMap F E x) = exp (-count E w (codiff E)) := by
  refine exp_count_eq codiff_ne_zero codiff_ne_zero (algebraMap F E) (fun t ht => ?_) (fun t ht => ?_)
    (fun s t e => by rw [valuation_up rfl, valuation_up rfl, e]) hx
  · refine (inD_iff _).1 fun o => ?_
    rw [← Algebra.trace_trace (S := F), mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    exact (inD_iff t).2 ht ⟨Algebra.trace F E o, Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)⟩
  · have : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ _ _
    have htop : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
      by_contra hn
      obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hn
      exact (not_dvd_differentIdeal_iff (A := 𝓞 F) (P := P)).2 inferInstance (Ideal.dvd_iff_le.2 hle)
    have e := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)
    rw [htop, Ideal.top_mul] at e
    rw [← coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)] at ht
    rw [← coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), e]
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ht
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨algebraMap _ _ c, Ideal.mem_map_of_mem _ hc, rfl⟩

theorem count_codiff_F {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {v : Pl F} (h : PsiUnr ψ v) : count F v (codiff F) = 0 := by
  obtain ⟨t, ht, et⟩ := exists_mem_valuation_eq (codiff_ne_zero (F := F)) v
  have h1 : algebraMap F (Fv F v) t ∈ v.adicCompletionIntegers F := (h _).1 fun y hy => by
    have hm : singleFin v (algebraMap F (Fv F v) t * y) ∈ adelicIdeal (codiff F) := fun u => by
      by_cases hu : u = v
      · subst hu
        rw [show (singleFin u (algebraMap F (Fv F u) t * y)) u = _ from evalV_singleFin_self u _, mul_comm]
        exact (localIdeal u (codiff F)).smul_mem ⟨y, hy⟩ (Submodule.subset_span ⟨t, ht, rfl⟩)
      · rw [show (singleFin v (algebraMap F (Fv F v) t * y)) u = _ from evalV_singleFin_ne hu _]
        exact zero_mem _
    have := (GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hψ) _).1 hm 1 fun u => one_mem _
    rw [one_mul] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap, et, ← exp_zero, exp_le_exp] at h1
  have h2 := (mem_iff_valuation_le (codiff_ne_zero (F := F)) 1).1
    (FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)) v
  rw [map_one, ← exp_zero, exp_le_exp] at h2
  omega

theorem pr_codiff {B : Base F E} (hB : B.IsGood σ) : Pr B.P (codiff E) := fun w hw => by
  have := codiff_up hB.unram (w := w) (x := 1) (by rw [count_codiff_F hB.std (hB.psiP _ hw)]; simp)
  rw [map_one, map_one, ← exp_zero, exp_inj] at this
  omega

theorem idealVal_codiff {B : Base F E} (hB : B.IsGood σ) {ν : Chr F E} (hν : ∀ a : (AF F)ˣ, ν (ideleMap F E a) = 1)
    (hu : UnrOff ν (B.P : Set (Pl F))) : idealVal ν (codiff E) = 1 := by
  classical
  have hf : {v : Pl F | count F v (codiff F) ≠ 0}.Finite := FractionalIdeal.finite_factors _
  let a : Pl F → Fˣ := fun v => unif v ^ count F v (codiff F)
  have ha : ∀ v, v.valuation F (a v : F) = exp (-count F v (codiff F)) := fun v => by
    have := unif_spec v
    unfold IsUnifAt at this
    have e : v.valuation F (unif v : F) = exp (-1 : ℤ) := (valued_algebraMap v _).symm.trans this
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, e, ← exp_zsmul, smul_eq_mul, mul_neg, mul_one]
  let l : (AE F E)ˣ := ∏ v ∈ hf.toFinset, ideleMap F E (Neutral.B1.localIdele F v (atFin v (a v)))
  have hc : ∀ w : HeightOneSpectrum (𝓞 E), cp F w (l : AE F E) = if w.under (𝓞 F) ∈ hf.toFinset then algebraMap E _ (algebraMap F E (a (w.under (𝓞 F)))) else 1 := fun w => by
    rw [Units.coe_prod, map_prod]
    simp only [ideleMap_localIdele, cp_prod, mem_aboveF]
    rw [Finset.prod_ite_eq]
    rfl
  have G : Gen B.P (codiff E) hf.toFinset l := by
    refine ⟨fun v hv hP => hf.mem_toFinset.1 hv (count_codiff_F hB.std (hB.psiP _ hP)), ?_,
      fun v hv => ext_cp (by rw [inf_idem, inf_idem]) fun w => ?_, fun w => ?_⟩
    · rw [Units.coe_prod, map_prod]
      exact Finset.prod_eq_one fun v _ => by rw [ideleMap_localIdele, inf_prod]
    · by_cases hw : w.under (𝓞 F) = v
      · rw [cp_idem hw, cp_idem hw, hc, if_neg (hw ▸ hv), map_one]
      · rw [cp_idem_ne hw, cp_idem_ne hw]
    · rw [hc]
      split_ifs with hw
      · rw [valued_algebraMap]; exact codiff_up hB.unram (ha _)
      · have h0 : count F (w.under (𝓞 F)) (codiff F) = 0 := by by_contra hn; exact hw (hf.mem_toFinset.2 hn)
        have := codiff_up hB.unram (w := w) (x := 1) (by rw [h0]; simp)
        rw [map_one, map_one] at this
        rw [map_one, this]
  rw [← G.eq hu, map_prod, Finset.prod_eq_one fun v _ => hν _, map_one]

variable (hσ : ∀ x, σ (σ x) = x)

theorem count_bar {v : Pl F} (τ : E →ₐ[F] Fv F v) {𝔞 : FI E} (h0 : 𝔞 ≠ 0) :
    count E (splitPrime (τ.comp σ)) 𝔞 = count E (splitPrime τ) (cj hσ 𝔞) := by
  obtain ⟨s, -, es⟩ := exists_mem_valuation_eq h0 (splitPrime (τ.comp σ))
  have e : ∀ s, (splitPrime τ).valuation E ((σ : E →+* E) s) = (splitPrime (τ.comp σ)).valuation E s := fun s => by
    rw [← valued_apply_eq_valuation, ← valued_apply_eq_valuation]; rfl
  have := exp_count_eq h0 (cj_ne hσ h0) (σ : E →+* E) (fun t ht => (mem_cj hσ).2 (by rwa [RingHom.coe_coe, hσ]))
    (fun t ht => by rw [← cj_inv hσ h0]; exact (mem_cj hσ).2 (by rwa [RingHom.coe_coe, hσ]))
    (w := splitPrime τ) (fun s t h => by rw [e, e, h]) es
  rw [e, es, exp_inj] at this
  omega

theorem pr_of {B : Base F E} (h : IsCMExt F E σ) {𝔞 : FI E}
    (H : ∀ v : B.P, count E (splitPrime (B.τ v)) 𝔞 = 0 ∧ count E (splitPrime ((B.τ v).comp σ)) 𝔞 = 0) : Pr B.P 𝔞 := fun w hw => by
  have : w.asIdeal ∈ (w.under (𝓞 F)).asIdeal.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩
  rw [primesOver_eq_split h (B.τ ⟨_, hw⟩)] at this
  rcases this with e | e
  · rw [HeightOneSpectrum.ext e]; exact (H ⟨_, hw⟩).1
  · rw [HeightOneSpectrum.ext e]; exact (H ⟨_, hw⟩).2

theorem Pr.cj {B : Base F E} (h : IsCMExt F E σ) {𝔞 : FI E} (h0 : 𝔞 ≠ 0) (H : Pr B.P 𝔞) : Pr B.P (cj hσ 𝔞) :=
  pr_of h fun v => ⟨by rw [← count_bar hσ _ h0]; exact H _ (by rw [splitPrime_under]; exact v.2),
    by rw [count_bar hσ _ (cj_ne hσ h0), cj_cj]; exact H _ (by rw [splitPrime_under]; exact v.2)⟩

theorem Pr.mul {P : Finset (Pl F)} {𝔞 𝔟 : FI E} (ha : 𝔞 ≠ 0) (hb : 𝔟 ≠ 0) (h : Pr P 𝔞) (h' : Pr P 𝔟) : Pr P (𝔞 * 𝔟) :=
  fun w hw => by rw [FractionalIdeal.count_mul _ _ ha hb, h w hw, h' w hw, add_zero]

theorem Pr.inv {P : Finset (Pl F)} {𝔞 : FI E} (h : Pr P 𝔞) : Pr P 𝔞⁻¹ :=
  fun w hw => by rw [FractionalIdeal.count_inv, h w hw, neg_zero]

structure Line {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) (𝔭 : FI E) : Prop where
  ne : 𝔭 ≠ 0
  mem : ∀ s ∈ 𝔭, s • x ∈ L
  ex : ∃ p : Fin n → E, x ⬝ᵥ p = 1 ∧ ∀ z ∈ L, z ⬝ᵥ p ∈ 𝔭

theorem Line.count_eq {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} {𝔭 : FI E} (h : Line L x 𝔭) {v : Pl F}
    {τ : E →ₐ[F] Fv F v} {β : GL (Fin n) (Fv F v)} (hβ : IsSplitBasis τ L β) (i : Fin n) (hi : ∀ r, β.1 r i = τ (x r)) :
    count E (splitPrime τ) 𝔭 = 0 := by
  classical
  obtain ⟨p, hp, hL⟩ := h.ex
  have col : ∀ c : Fv F v, β.1 *ᵥ Pi.single i c = fun r => c * τ (x r) := fun c => by
    ext r; rw [Matrix.mulVec_single]; simp [hi, mul_comm]
  have a1 : ∀ u ∈ splitLat τ L, Valued.v (u ⬝ᵥ fun r => τ (p r)) ≤ exp (-count E (splitPrime τ) 𝔭) := by
    rintro _ ⟨y, hy, rfl⟩
    refine latLoc_induction (p := fun y => Valued.v (splitVec τ y ⬝ᵥ fun r => τ (p r)) ≤ exp (-count E (splitPrime τ) 𝔭))
      (fun a ha z hz => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy
    · have : (splitVec τ (fun i => a ⊗ₜ[F] z i) ⬝ᵥ fun r => τ (p r)) = a * τ (z ⬝ᵥ p) := by
        simp [splitVec, dotProduct, Finset.mul_sum, mul_assoc]
      rw [this, map_mul, valued_apply_eq_valuation]
      exact (mul_le_of_le_one_left' ha).trans ((mem_iff_valuation_le h.ne _).1 (hL z hz) _)
    · simp [splitVec, dotProduct]
    · rw [splitVec_add, add_dotProduct]; exact (Valuation.map_add _ _ _).trans (max_le hy hz)
    · have : splitVec τ (-y) = -splitVec τ y := funext fun r => map_neg _ _
      rwa [this, neg_dotProduct, Valuation.map_neg]
  have a2 := a1 _ ((hβ (Pi.single i 1)).1 fun j => by
    by_cases e : j = i
    · subst e; simp
    · simp [e])
  have e2 : ((fun r => 1 * τ (x r)) ⬝ᵥ fun r => τ (p r)) = 1 := by
    have := congrArg τ hp
    simpa [dotProduct] using this
  rw [col, e2, map_one, ← exp_zero, exp_le_exp] at a2
  obtain ⟨s, hs, es⟩ := exists_mem_valuation_eq h.ne (splitPrime τ)
  have a3 := (hβ (Pi.single i (τ s))).2 (by
    rw [col]
    exact ⟨_, tmul_mem_latLoc (one_mem _) (h.mem s hs), funext fun r => by simp [splitVec]⟩) i
  rw [Pi.single_eq_same, HeightOneSpectrum.mem_adicCompletionIntegers, valued_apply_eq_valuation, es, ← exp_zero,
    exp_le_exp] at a3
  omega

theorem line_lat {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {x : Fin n → E} {y : Fin d → E} {𝔭 𝔮 : FI E} (hx : Line X.L x 𝔭)
    (hy : Line W.L y 𝔮) (v : Pl F) (c : AE F E) :
    c • Matrix.vecMulVec (incV F x) (incV F y) ∈ latAtV X W v ↔ c ∈ Lat (𝔭 * 𝔮) v := by
  constructor
  · intro h
    obtain ⟨p, hp, hL⟩ := hx.ex
    obtain ⟨q, hq, hM⟩ := hy.ex
    have inc : ∀ {m : ℕ} (a b : Fin m → E), incV F a ⬝ᵥ incV F b = inclR (F := F) (AF F) (a ⬝ᵥ b) := fun a b => by
      simp [incV, dotProduct]
    have key : ∀ (x' : Fin n → E) (y' : Fin d → E), incV F p ⬝ᵥ Matrix.vecMulVec (incV F x') (incV F y') *ᵥ incV F q =
        inclR (F := F) (AF F) (x' ⬝ᵥ p * y' ⬝ᵥ q) := fun x' y' => by
      rw [Matrix.vecMulVec_mulVec, dotProduct_smul, inc, inc, map_mul, dotProduct_comm p]
      simp [mul_comm]
    have : ∀ Z ∈ latAtV X W v, incV F p ⬝ᵥ Z *ᵥ incV F q ∈ Lat (𝔭 * 𝔮) v := fun Z hZ => by
      induction hZ using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, h1, h2, x', hx', y', hy', rfl⟩ := hz
        have e : incM F (Matrix.vecMulVec x' y') = Matrix.vecMulVec (incV F x') (incV F y') := by
          ext i j; exact map_mul (inclR (F := F) (AF F)) _ _
        rw [e, Matrix.smul_mulVec, dotProduct_smul, key]
        refine AddSubgroup.subset_closure ⟨a, h1, h2, _, FractionalIdeal.mul_mem_mul (hL _ hx') (hM _ hy'), ?_⟩
        change a • ((1 : AF F) ⊗ₜ[F] _) = _
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | zero => rw [Matrix.zero_mulVec, dotProduct_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [Matrix.add_mulVec, dotProduct_add]; exact add_mem ha hb
      | neg a _ ha => rw [Matrix.neg_mulVec, dotProduct_neg]; exact neg_mem ha
    have := this _ h
    rwa [Matrix.smul_mulVec, dotProduct_smul, key, hp, hq, mul_one, map_one, smul_eq_mul, mul_one] at this
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, h1, h2, s, hs, rfl⟩ := hz
      refine FractionalIdeal.mul_induction_on
        (C := fun s => (a ⊗ₜ[F] s : AE F E) • Matrix.vecMulVec (incV F x) (incV F y) ∈ latAtV X W v) hs ?_ ?_
      · intro s hs t ht
        refine AddSubgroup.subset_closure ⟨a, h1, h2, _, hx.mem s hs, _, hy.mem t ht, ?_⟩
        ext i j
        change (a ⊗ₜ[F] (s * t)) * (((1 : AF F) ⊗ₜ[F] x i) * ((1 : AF F) ⊗ₜ[F] y j)) = a • ((1 : AF F) ⊗ₜ[F] (s * x i * (t * y j)))
        rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
        congr 1 <;> ring
      · intro s t hs ht
        rw [TensorProduct.tmul_add, add_smul]; exact add_mem hs ht
    | zero => rw [zero_smul]; exact zero_mem _
    | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
    | neg a _ ha => rw [neg_smul]; exact neg_mem ha

theorem plane_lines {B : Base F E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i j : ℕ} {ε : E} {D : FI E}
    (hε : ε * ε = 1) (hJ : ∀ i j, σ (Y.J j i) = ε * Y.J i j) (hl : Y.L.IsLattice E)
    (hd : ∀ y, y ∈ Y.L ↔ ∀ x ∈ Y.L, form σ Y.J y x ∈ D) (hD : D ≠ 0) (h : H.IsAdapted σ B Y Y₁ i j) :
    Line Y.L H.x H.𝔟 ∧ Line Y.L H.y (D * (cj hσ H.𝔟)⁻¹) := by
  have sym : ∀ u w, form σ Y.J w u = ε * σ (form σ Y.J u w) := fun u w => by
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, hJ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    linear_combination (-(w b * Y.J b a * σ (u a))) * hε
  have fl : ∀ (s t : E) u w, form σ Y.J (s • H.x + H.ι *ᵥ u + t • H.y) w =
      s * form σ Y.J H.x w + form σ Y.J (H.ι *ᵥ u) w + t * form σ Y.J H.y w := fun s t u w => by
    simp only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have yx : form σ Y.J H.y H.x = ε := by rw [sym, h.xy, map_one, mul_one]
  have f1 : ∀ (s t : E) u, form σ Y.J (s • H.x + H.ι *ᵥ u + t • H.y) H.y = s := fun s t u => by
    rw [fl, h.xy, (h.orth u).2, h.yy]; ring
  have f2 : ∀ (s t : E) u, form σ Y.J (s • H.x + H.ι *ᵥ u + t • H.y) H.x = t * ε := fun s t u => by
    rw [fl, h.xx, (h.orth u).1, yx]; ring
  have hb : ∀ z ∈ Y.L, form σ Y.J z H.y ∈ H.𝔟 := fun z hz => by
    obtain ⟨s, t, u, hs, -, -, rfl⟩ := h.split z hz
    rw [f1]; exact (h.ideal s).2 hs
  have b0 : H.𝔟 ≠ 0 := fun e => by
    have : ∀ z ∈ Submodule.span E (Y.L : Set (Fin n → E)), form σ Y.J z H.y = 0 := fun z hz => by
      induction hz using Submodule.span_induction with
      | mem z hz => have := hb z hz; rwa [e, FractionalIdeal.mem_zero_iff] at this
      | zero => simp [form]
      | add a b _ _ ha hb => simp only [form, add_dotProduct] at *; rw [ha, hb, add_zero]
      | smul a b _ hb => simp only [form, smul_dotProduct] at *; rw [hb, smul_zero]
    have := this H.x (hl.span_eq_top ▸ Submodule.mem_top)
    rw [h.xy] at this
    exact one_ne_zero this
  have εD : ∀ t, t * ε ∈ D ↔ t ∈ D := by
    have : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.1 hε
    rcases this with rfl | rfl
    · simp
    · intro t; rw [mul_neg, mul_one]; exact D.val.neg_mem_iff
  have my : ∀ t, t ∈ D * (cj hσ H.𝔟)⁻¹ ↔ t • H.y ∈ Y.L := fun t => by
    rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero (cj_ne hσ b0), hd]
    have g : ∀ z, form σ Y.J (t • H.y) z = t * σ (form σ Y.J z H.y) * ε := fun z => by
      have := sym z H.y
      simp only [form, smul_dotProduct, smul_eq_mul] at *
      rw [this]; ring
    constructor
    · intro H1 z hz
      rw [g, εD]
      exact H1 _ ((mem_cj hσ).2 (by rw [hσ]; exact hb z hz))
    · intro H1 s hs
      have := H1 _ ((h.ideal _).1 hs)
      rw [g, εD] at this
      have e : form σ Y.J (σ s • H.x) H.y = σ s := by
        have e0 := h.xy
        simp only [form, smul_dotProduct, smul_eq_mul] at e0 ⊢
        rw [e0, mul_one]
      rwa [e, hσ] at this
  refine ⟨⟨b0, fun s hs => (h.ideal s).1 hs, _, h.xy, hb⟩,
    ⟨mul_ne_zero hD (inv_ne_zero (cj_ne hσ b0)), fun t ht => (my t).1 ht, ε • Y.J *ᵥ fun i => σ (H.x i), ?_, fun z hz => ?_⟩⟩
  · rw [dotProduct_smul]; change ε * form σ Y.J H.y H.x = 1; rw [yx, hε]
  · rw [dotProduct_smul]; change ε * form σ Y.J z H.x ∈ _
    obtain ⟨s, t, u, -, ht, -, rfl⟩ := h.split z hz
    rw [f2, mul_left_comm, hε, mul_one]; exact (my t).2 ht

theorem plane_pr {B : Base F E} (hc : IsCMExt F E σ) {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i j : ℕ} {D : FI E}
    (hD : D ≠ 0) (pD : Pr B.P D) (hb : ∀ v : B.P, IsSplitBasis (B.τ v) Y.L (Y.bas v)) (h : H.IsAdapted σ B Y Y₁ i j) (hi : i < n) (hj : j < n)
    (l : Line Y.L H.x H.𝔟 ∧ Line Y.L H.y (D * (cj hσ H.𝔟)⁻¹)) : Pr B.P H.𝔟 :=
  pr_of hc fun v => by
    refine ⟨l.1.count_eq (hb v) ⟨i, hi⟩ ((h.bas v _).1 rfl), ?_⟩
    have := l.2.count_eq (hb v) ⟨j, hj⟩ ((h.bas v _).2.1 rfl)
    rw [FractionalIdeal.count_mul _ _ hD (inv_ne_zero (cj_ne hσ l.1.ne)), FractionalIdeal.count_inv,
      pD _ (by rw [splitPrime_under]; exact v.2), ← count_bar hσ _ l.1.ne] at this
    omega

end PositivityTheory.ThKG.Loc.Cone.Id

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Id

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes WithZero
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Idele
open Formalism.L2.Host (IsUnitAt IsUnifAt atFin unif unif_spec)
open FractionalIdeal (count)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem lines {B : Base F E} (hB : B.IsGood σ) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {H : Plane E n n₁} {H' : Plane E d d₁} {r s r' s' i j i' j' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (h : H.IsAdapted σ B X X₁ i j) (h' : H'.IsAdapted σ B W W₁ i' j') (hσ : ∀ x, σ (σ x) = x) :
    (Line X.L H.x H.𝔟 ∧ Line X.L H.y (1 * (cj hσ H.𝔟)⁻¹)) ∧
      Line W.L H'.x H'.𝔟 ∧ Line W.L H'.y (codiff E * (cj hσ H'.𝔟)⁻¹) :=
  ⟨plane_lines hσ (ε := 1) (mul_one 1) (fun a b => by rw [hX.herm, one_mul]) hX.lat (fun y => by
      rw [hX.dual]
      refine forall₂_congr fun x _ => ?_
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨fun e => ⟨⟨_, e⟩, rfl⟩, fun ⟨o, e⟩ => e ▸ RingOfIntegers.isIntegral_coe o⟩) one_ne_zero h,
    plane_lines hσ (ε := -1) (by ring) (fun a b => by rw [hW.skew, neg_one_mul]) hW.lat (fun y => by
      rw [hW.dual]
      exact forall₂_congr fun x _ => inD_iff _) codiff_ne_zero h'⟩

theorem memA {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {H : Plane E n n₁} {H' : Plane E d d₁} {𝔭 𝔮 : FI E}
    (a : Line X.L H.x 𝔭) (b : Line W.L H'.y 𝔮) (v : Pl F) (l : (AE F E)ˣ) :
    idem F v • shiftA H H' l ∈ latAtV X W v ↔ InAt (𝔭 * 𝔮) v (l : AE F E) := by
  rw [shiftA, ← smul_assoc, line_lat a b, lat_iff (mul_ne_zero a.ne b.ne)]

theorem memB (hσ : ∀ x, σ (σ x) = x) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {H : Plane E n n₁} {H' : Plane E d d₁}
    {𝔭 𝔮 : FI E} (a : Line X.L H.y 𝔭) (b : Line W.L H'.x 𝔮) (v : Pl F) (l : (AE F E)ˣ) :
    idem F v • shiftB σ H H' l ∈ latAtV X W v ↔ InAt (cj hσ (𝔭 * 𝔮)) v (l : AE F E) := by
  rw [shiftB, ← smul_assoc, line_lat a b, lat_iff (mul_ne_zero a.ne b.ne), inAt_cj_iff hσ (mul_ne_zero a.ne b.ne)]

theorem idealId0 : IdealId0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' r s r' s' i j i' j' hB hX hW h h' u hu
  have hσ := PositivityTheory.ThK.Vac.sigma_sigma hB.cm
  obtain ⟨⟨a, a'⟩, b, b'⟩ := lines hB hX hW h h' hσ
  rcases hu with rfl | rfl
  · exact ⟨_, mul_ne_zero a.ne b'.ne, memA a b'⟩
  · exact ⟨_, cj_ne hσ (mul_ne_zero a'.ne b.ne), memB hσ a' b⟩

theorem idealId' : IdealId' := by
  refine ⟨1, 1, -1, -1, ?_⟩
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' r s r' s' i j i' j' hB hX hW h h' hi hj hi' hj' u e₁ e₂ hu
  have hσ := PositivityTheory.ThK.Vac.sigma_sigma hB.cm
  obtain ⟨⟨a, a'⟩, b, b'⟩ := lines hB hX hW h h' hσ
  have pD := pr_codiff hB
  have p1 : Pr B.P (1 : FI E) := fun w _ => FractionalIdeal.count_one _ _
  have pa := plane_pr hσ hB.cm one_ne_zero p1 hX.bas h hi hj ⟨a, a'⟩
  have pb := plane_pr hσ hB.cm codiff_ne_zero pD hW.bas h' hi' hj' ⟨b, b'⟩
  have ca := cj_ne hσ a.ne
  have cb := cj_ne hσ b.ne
  have tr : ∀ ν : Chr F E, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range ν 0 →
      ∀ x : (AF F)ˣ, ν (ideleMap F E x) = 1 := fun ν hν x => hν.triv_of_even Even.zero x
  rcases hu with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨_, mul_ne_zero a.ne b'.ne, memA a b',
      pa.mul a.ne b'.ne (pD.mul codiff_ne_zero (inv_ne_zero cb) (pb.cj hσ hB.cm b.ne).inv), fun ν _ hν hu => ?_⟩
    rw [idealVal_mul _ a.ne b'.ne, idealVal_mul _ codiff_ne_zero (inv_ne_zero cb), idealVal_inv,
      idealVal_cj hσ b.ne pb hu (nu_conj hB.cm (tr ν hν)), idealVal_codiff hB (tr ν hν) hu]
    simp
  · have pp : Pr B.P (1 * (cj hσ H.𝔟)⁻¹ * H'.𝔟) :=
      (p1.mul (one_ne_zero (α := FI E)) (inv_ne_zero ca) (pa.cj hσ hB.cm a.ne).inv).mul a'.ne b.ne pb
    refine ⟨_, cj_ne hσ (mul_ne_zero a'.ne b.ne), memB hσ a' b, pp.cj hσ hB.cm (mul_ne_zero a'.ne b.ne), fun ν _ hν hu => ?_⟩
    rw [idealVal_cj hσ (mul_ne_zero a'.ne b.ne) pp hu (nu_conj hB.cm (tr ν hν)), idealVal_mul _ a'.ne b.ne, one_mul, idealVal_inv,
      idealVal_cj hσ a.ne pa hu (nu_conj hB.cm (tr ν hν))]
    simp [mul_comm]

end PositivityTheory.ThKG.Loc.Cone.Id

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF

theorem vacShift_of (h : FinCone2) : VacShift := fun F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev a b v =>
  (h F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev a b v).1

theorem finM_of (h : FinCone2) : FinM := fun F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev a b v =>
  (h F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev a b v).2.2

theorem coneFac_all (hA : ActsEx) (hSt : StabEx) (hO : ArchOp) (hU : ArchUniq) (hPS : PositivityTheory.Mix.PureSt) (hAr : ArchCone) (v : VacFixX) :
    PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation ∧ ConeFacA ∧ ConeFacB := by
  have f := Fin.finCone2_of ideleFub Id.idealId0 hSt
  have p := pureFac_of hA hO hU v (vacShift_of f) hPS
  have a := coneIntegralFactorisation_of hA ideleFub (kFub_of hSt) v (vacShift_of f) hAr (finM_of f) p Fin.schSpan Id.idealId'
  exact ⟨a, coneFactorisation_of_codimension_two a, coneFacB_of hA ideleFub (kFub_of hSt) v (vacShift_of f) hAr (finM_of f) p Fin.schSpan Id.idealId'⟩

end PositivityTheory.ThKG.Loc.Cone

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF

theorem coneFac_of (hA : ActsEx) (hSt : StabEx) (hO : ArchOp) (hU : ArchUniq) (hPS : PositivityTheory.Mix.PureSt) (hAr : ArchCone) :
    MeasEx ∧ PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation ∧ ConeFacA ∧ ConeFacB :=
  ⟨measEx_of hSt, coneFac_all hA hSt hO hU hPS hAr (vacFixX_of hSt)⟩

end PositivityTheory.ThKG.Loc.Cone

end
end
