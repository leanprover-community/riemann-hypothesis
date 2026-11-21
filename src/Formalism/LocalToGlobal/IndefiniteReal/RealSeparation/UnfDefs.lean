import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.ParabSt

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def embS (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (M : Mx D T.rank ρ) : WO S T :=
  HMul.hMul M ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram).map (incA D))

def embP (S T : HSp D) {ρ : ℕ} (CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (M' : Mx D T.rank ρ) : WO S T :=
  HMul.hMul M' ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS' * S.gram).map (incA D))

def embQ (S T S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (x : WO S0 T) : WO S T :=
  HMul.hMul x ((S0.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) BS * S.gram).map (incA D))

def ellS (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (F : WO S T → ℂ) : ℂ :=
  ∫ M in 𝓕, F (embS S T CS M) ∂μ

def RedS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (F : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ellS S T CS μ 𝓕 (heisO ψ S T w F)

def descS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (S0 : HSp D)
    (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (f : WO S T → ℂ) : WO S0 T → ℂ :=
  fun x => RedS ψ S T CS μ 𝓕 f (embQ S T S0 BS x)

def IsDescSOf (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (om0 : GA D S0 × GA D T →* Module.End ℂ (WO S0 T → ℂ)) : Prop :=
  ∀ g0 g h, IsLeviEmb S CS CS' S0 BS g0 g → ∀ f, IsThetaFunO ψ S T f →
    descS ψ S T CS μ 𝓕 S0 BS (om (g, h) f) = om0 (g0, h) (descS ψ S T CS μ 𝓕 S0 BS f)

def DescSTheta (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∀ (ρ : ℕ) (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
      (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E), IsQuotFrame S CS CS' S0 BS →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ →
      ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S0 T (descS ψ S T CS μ 𝓕 S0 BS f)

def DescSWeil (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (ρ : ℕ) (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
      (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E), IsQuotFrame S CS CS' S0 BS →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ →
      ∃ om0 : GA D S0 × GA D T →* Module.End ℂ (WO S0 T → ℂ),
        IsWeilDatumO ψ S0 T χS χT om0 ∧ IsDescSOf ψ S T CS CS' S0 BS μ 𝓕 om om0

def ParabSN (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (ρ : ℕ) (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E), IsIsoFrame S CS →
      ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ →
        ∀ n ∈ NI S CS, ∀ f, IsThetaFunO ψ S T f → ∀ w,
          RedS ψ S T CS μ 𝓕 (om (n, 1) f) w = RedS ψ S T CS μ 𝓕 f (actO S T n⁻¹ 1 w)

def ParabSM1 (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (ρ : ℕ) (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E), IsIsoFrame S CS →
      ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ →
        ∀ g : GA D S, IsParI S CS g → ∀ (α : Fin ρ → D.host.E) (β : Fin ρ → AE D),
          ∑ i, β i * incA D (α i) = 0 →
          HMul.hMul (mt S g) (CS.map (incA D)) =
            HMul.hMul (CS.map (incA D)) (1 + Matrix.vecMulVec (fun i => incA D (α i)) β) →
          ∀ f, IsThetaFunO ψ S T f → ∀ w,
            RedS ψ S T CS μ 𝓕 (om (g, 1) f) w = RedS ψ S T CS μ 𝓕 f (actO S T g⁻¹ 1 w)

def MixedLawS (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (ρ : ℕ) (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
      (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E), IsQuotFrame S CS CS' S0 BS →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ →
      ∀ om0 : GA D S0 × GA D T →* Module.End ℂ (WO S0 T → ℂ), IsDescSOf ψ S T CS CS' S0 BS μ 𝓕 om om0 →
        ∀ g0 g h, IsLeviEmb S CS CS' S0 BS g0 g → ∀ f, IsThetaFunO ψ S T f →
          ∀ (M' : Mx D T.rank ρ) (x : WO S0 T),
            RedS ψ S T CS μ 𝓕 (om (g, h) f) (embP S T CS' M' + embQ S T S0 BS x) =
              om0 (g0, h) (fun x' => RedS ψ S T CS μ 𝓕 f
                (embP S T CS' (HMul.hMul (mt T h⁻¹) M') + embQ S T S0 BS x')) x

def HeisS (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ρ : ℕ)
    (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E), IsIsoFrame S CS →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∀ (M : Mx D T.rank ρ) w,
        RedS ψ S T CS μ 𝓕 (heisO ψ S T (embS S T CS M) f) w =
          ψ (symplO S T w (embS S T CS M)) * RedS ψ S T CS μ 𝓕 f w

def RedInvS (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∀ (ρ : ℕ) (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
      (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E), IsQuotFrame S CS CS' S0 BS →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ →
      ∀ f, IsThetaFunO ψ S T f →
        Summable (fun M' : Matrix (Fin T.rank) (Fin ρ) D.host.E =>
          ‖RedS ψ S T CS μ 𝓕 (heisO ψ S T (embP S T CS' (M'.map (incA D))) f) 0‖) ∧
        ((μ 𝓕).toReal : ℂ) * f 0 =
          ∑' M' : Matrix (Fin T.rank) (Fin ρ) D.host.E,
            RedS ψ S T CS μ 𝓕 (heisO ψ S T (embP S T CS' (M'.map (incA D))) f) 0

def modelA (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r ρ : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μ : Measure (Mx D r S.rank))
    (𝓕 : Set (Mx D r S.rank)) (μS : Measure (Mx D T0.rank ρ)) (𝓕S : Set (Mx D T0.rank ρ)) (f : WO S T → ℂ)
    (k : Mx D r ρ) (z : WO S0 T0) : ℂ :=
  RedS ψ S T0 CS μS 𝓕S
    (fun x0 => Red ψ S T C μ 𝓕 f (embI S T C' (HMul.hMul k
      ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram).map (incA D))) + embI S T B0 x0))
    (embQ S T0 S0 BS z)

def modelB (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r ρ : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μS' : Measure (Mx D T.rank ρ))
    (𝓕S' : Set (Mx D T.rank ρ)) (μ0 : Measure (Mx D r S0.rank)) (𝓕0 : Set (Mx D r S0.rank)) (f : WO S T → ℂ)
    (p : Mx D r ρ) (z : WO S0 T0) : ℂ :=
  Red ψ S0 T C μ0 𝓕0
    (fun x' => RedS ψ S T CS μS' 𝓕S' f (embP S T CS' (HMul.hMul (C.map (incA D)) p) + embQ S T S0 BS x'))
    (embI S0 T B0 z)

def TwoModel (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (r ρ : ℕ)
    (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E),
    IsQuotFrame T C C' T0 B0 →
    ∀ (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E),
    IsQuotFrame S CS CS' S0 BS →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ → μ 𝓕 = 1 →
    ∀ (μS : Measure (Mx D T0.rank ρ)) (𝓕S : Set (Mx D T0.rank ρ)), μS.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T0.rank ρ) 𝓕S μS → μS 𝓕S = 1 →
    ∀ (μS' : Measure (Mx D T.rank ρ)) (𝓕S' : Set (Mx D T.rank ρ)), μS'.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕S' μS' → μS' 𝓕S' = 1 →
    ∀ (μ0 : Measure (Mx D r S0.rank)) (𝓕0 : Set (Mx D r S0.rank)), μ0.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S0.rank) 𝓕0 μ0 → μ0 𝓕0 = 1 →
    ∀ (ν : Measure (Mx D r ρ)) (𝓕ν : Set (Mx D r ρ)), ν.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r ρ) 𝓕ν ν → ν 𝓕ν = 1 →
    ∀ f, IsThetaFunO ψ S T f → ∀ (p : Mx D r ρ) (z : WO S0 T0),
      Integrable (fun k : Mx D r ρ =>
        ψ (symplO S T (embI S T C' (HMul.hMul k
            ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram).map (incA D))))
          (embP S T CS' (HMul.hMul (C.map (incA D)) p))) *
        modelA ψ S T C C' T0 B0 CS S0 BS μ 𝓕 μS 𝓕S f k z) ν ∧
      modelB ψ S T C T0 B0 CS CS' S0 BS μS' 𝓕S' μ0 𝓕0 f p z =
        ∫ k, ψ (symplO S T (embI S T C' (HMul.hMul k
            ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram).map (incA D))))
          (embP S T CS' (HMul.hMul (C.map (incA D)) p))) *
        modelA ψ S T C C' T0 B0 CS S0 BS μ 𝓕 μS 𝓕S f k z ∂ν

example (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) : IsDescSOf ψ S T CS CS' S0 BS μ 𝓕 1 1 := by
  intro g0 g h _ f _
  simp

end Formalism.IndefR.Mi

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsCutoff (S S0 : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (lev : GA D S0 →* GA D S)
    (μN : Measure (NI S CS)) (μ0 : Measure (GA D S0)) (β : GA D S → ℝ) : Prop :=
  (∀ h, 0 ≤ β h) ∧ Measurable β ∧ ∀ h,
    Integrable (fun p : NI S CS × GA D S0 => β ((p.1 : GA D S) * lev p.2 * h)) (μN.prod μ0) ∧
      ∫ p, β ((p.1 : GA D S) * lev p.2 * h) ∂(μN.prod μ0) = 1

def cutInt (S : HSp D) (ν : Measure (GA D S)) (β : GA D S → ℝ) (Φ : GA D S → ℂ) : ℂ :=
  ∫ h, (β h : ℂ) * Φ h ∂ν

def MU (S : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
    (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) : Subgroup (GA D S) :=
  Subgroup.closure {g | ∃ u : Matrix (Fin ρ) (Fin ρ) (AE D), (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧
    HMul.hMul (mt S g) (CS.map (incA D)) = HMul.hMul (CS.map (incA D)) u ∧
    HMul.hMul (mt S g) (BS.map (incA D)) = BS.map (incA D) ∧
    ∃ v : Matrix (Fin ρ) (Fin ρ) (AE D), HMul.hMul (mt S g) (CS'.map (incA D)) = HMul.hMul (CS'.map (incA D)) v}

def MUQ (S : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
    (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) : Subgroup (MU S CS CS' S0 BS) :=
  (GQ S).subgroupOf (MU S CS CS' S0 BS)

def IsPsiUVal (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (g : GA D S) (v : ℂ) : Prop :=
  ∃ u : Matrix (Fin ρ) (Fin ρ) (AE D), HMul.hMul (mt S g) (CS.map (incA D)) = HMul.hMul (CS.map (incA D)) u ∧
    v = ψ (Algebra.trace (AF D.host.F) (AE D) (∑ i : Fin ρ, ∑ j : Fin ρ, if j.1 = i.1 + 1 then u i j else 0))

open Classical in

def psiU (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (g : GA D S) : ℂ :=
  if h : ∃ v, IsPsiUVal ψ S CS g v then h.choose else 1

def mixedModelBasePoint (S : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) : Mx D ρ S.rank :=
  (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram).map (incA D)

def yMat (T0 : HSp D) (ρ : ℕ) (ε : D.host.E) (z0 : Fin T0.rank → D.host.E) : Mx D T0.rank ρ :=
  fun i j => if j.1 + 1 = ρ then incA D (ε * D.host.xi0⁻¹ * z0 i) else 0

def jac (ψ : AddChar (AF D.host.F) ℂ) (S T0 : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (My : Mx D T0.rank ρ) (n : GA D S)
    (Ξ : WO S0 T0 → ℂ) : WO S0 T0 → ℂ :=
  fun x =>
    let w₁ : WO S T0 := HMul.hMul (embP S T0 CS' My + embQ S T0 S0 BS x) (mt S n)
    ψ (symplOH S T0 (embP S T0 CS' My + embQ S T0 S0 BS (HMul.hMul w₁ (BS.map (incA D))))
        (embS S T0 CS (HMul.hMul w₁ (CS'.map (incA D))))) *
      Ξ (HMul.hMul w₁ (BS.map (incA D)))

def xiEv (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (C C' : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (μS : Measure (Mx D T0.rank ρ)) (𝓕S : Set (Mx D T0.rank ρ)) (My : Mx D T0.rank ρ)
    (f : WO S T → ℂ) : WO S0 T0 → ℂ :=
  fun z => RedS ψ S T0 CS μS 𝓕S (fun x0 => Red ψ S T C μ 𝓕 f (embI S T C' (mixedModelBasePoint S CS) + embI S T B0 x0))
    (embP S T0 CS' My + embQ S T0 S0 BS z)

def bIntd (ψ : AddChar (AF D.host.F) ℂ) (S T0 : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (A : HSp D) (lev : GA D S0 →* GA D S)
    (ιH : GA D A →* GA D T0) (om00 : GA D S0 × GA D T0 →* Module.End ℂ (WO S0 T0 → ℂ)) (My : Mx D T0.rank ρ)
    (φ : GA D A → ℂ) (Ξ : WO S0 T0 → ℂ) (G' : GA D S → ℂ) (h'0 : GA D S0) (n : NI S CS)
    (m : MU S CS CS' S0 BS) (h0 : GA D A) : ℂ :=
  G' ((n : GA D S) * (m : GA D S) * lev h'0) * star (psiU ψ S CS (m : GA D S)) * φ h0 *
    jac ψ S T0 CS CS' S0 BS My (n : GA D S) (om00 (h'0, ιH h0) Ξ) 0

def bSharp (ψ : AddChar (AF D.host.F) ℂ) (S T0 : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (A : HSp D) (lev : GA D S0 →* GA D S)
    (ιH : GA D A →* GA D T0) (om00 : GA D S0 × GA D T0 →* Module.End ℂ (WO S0 T0 → ℂ)) (My : Mx D T0.rank ρ)
    (μ0 : Measure (GA D S0)) (𝓕0 : Set (GA D S0)) (μN : Measure (NI S CS)) (𝓕N : Set (NI S CS))
    (μU : Measure (MU S CS CS' S0 BS)) (𝓕U : Set (MU S CS CS' S0 BS)) (μH : Measure (GA D A)) (𝓕H : Set (GA D A))
    (φ : GA D A → ℂ) (Ξ : WO S0 T0 → ℂ) (G' : GA D S → ℂ) : ℂ :=
  ∫ h'0 in 𝓕0, ∫ n in 𝓕N, ∫ m in 𝓕U, ∫ h0 in 𝓕H,
    bIntd ψ S T0 CS CS' S0 BS A lev ιH om00 My φ Ξ G' h'0 n m h0 ∂μH ∂μU ∂μN ∂μ0

def BSharpAbs (ψ : AddChar (AF D.host.F) ℂ) (S T0 : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (A : HSp D) (lev : GA D S0 →* GA D S)
    (ιH : GA D A →* GA D T0) (om00 : GA D S0 × GA D T0 →* Module.End ℂ (WO S0 T0 → ℂ)) (My : Mx D T0.rank ρ)
    (μ0 : Measure (GA D S0)) (𝓕0 : Set (GA D S0)) (μN : Measure (NI S CS)) (𝓕N : Set (NI S CS))
    (μU : Measure (MU S CS CS' S0 BS)) (𝓕U : Set (MU S CS CS' S0 BS)) (μH : Measure (GA D A)) (𝓕H : Set (GA D A))
    (φ : GA D A → ℂ) (Ξ : WO S0 T0 → ℂ) (G' : GA D S → ℂ) : Prop :=
  Integrable (fun q : GA D S0 × NI S CS × MU S CS CS' S0 BS × GA D A =>
      bIntd ψ S T0 CS CS' S0 BS A lev ιH om00 My φ Ξ G' q.1 q.2.1 q.2.2.1 q.2.2.2)
    ((μ0.restrict 𝓕0).prod ((μN.restrict 𝓕N).prod ((μU.restrict 𝓕U).prod (μH.restrict 𝓕H))))

example (S S0 : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (lev : GA D S0 →* GA D S)
    (μN : Measure (NI S CS)) (μ0 : Measure (GA D S0)) [IsProbabilityMeasure (μN.prod μ0)] :
    IsCutoff S S0 CS lev μN μ0 (fun _ => 1) :=
  ⟨fun _ => zero_le_one, measurable_const, fun _ => ⟨integrable_const _, by simp⟩⟩

end Formalism.IndefR.Mi

end
end
