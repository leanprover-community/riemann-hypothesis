import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.DampedFunctionalEquationAtPoint

section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.K.GL2LocalData

section G

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def rWm (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (g : Matrix (Fin 2) (Fin 2) F) :
    (E → ℂ) → E → ℂ :=
  rW χ σ μE lam (g 0 0) (g 0 1) (g 1 0) (g 1 1)

def FTs (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (Φ : E → ℂ) (u : E) : ℂ :=
  ∫ z, Φ z * (χ (Algebra.trace F E (σ u * z)) : ℂ) ∂μE

open Classical in

def piG (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (g : GL (Fin 2) F)
    (Φ : E → ℂ) (x : E) : ℂ :=
  if h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det then
    ((c h.choose : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
      rW χ σ μE lam (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1)
        (fun y => Φ (y * (h.choose : E))) x
  else 0

open Classical in
variable (E) in

def nfib (f : E → ℂ) (a : Fˣ) : ℂ := if h : ∃ t : Eˣ, Algebra.norm F (t : E) = a then f (h.choose : E) else 0

variable (E) in

def SBE : Set (E → ℂ) := {Φ | IsLocallyConstant Φ ∧ HasCompactSupport Φ}

def cjA (A : F) (g : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F := !![g 0 0, A * g 0 1; g 1 0 / A, g 1 1]

end G

section WF

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]

variable (E) in

abbrev muE (χ : AddChar F Circle) : Measure E := selfDualMeasure (chE E χ)

variable (E) in

abbrev rWE (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (η : Fˣ →* ℂˣ) : Matrix (Fin 2) (Fin 2) F → (E → ℂ) → E → ℂ :=
  rWm χ σ (muE E χ) (lamE E χ η)
variable (E) in
abbrev WcE (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (η : Fˣ →* ℂˣ) (c : Eˣ →* ℂˣ) : (E → ℂ) → GL (Fin 2) F → ℂ :=
  Wc χ σ (muE E χ) (lamE E χ η) c
variable (E) in
abbrev piE (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (η : Fˣ →* ℂˣ) (c : Eˣ →* ℂˣ) : GL (Fin 2) F → (E → ℂ) → E → ℂ :=
  piG χ σ (muE E χ) (lamE E χ η) c
variable (E) in
abbrev FTE (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) : (E → ℂ) → E → ℂ := FTs χ σ (muE E χ)

variable (F E) in

def FibProp (κ : ℝ) : Prop :=
  ∀ f : E → ℂ, Continuous (fun x : Eˣ => f x) → (∀ (x : E) (u : Eˣ), Algebra.norm F (u : E) = 1 → f (x * u) = f x) →
    (Integrable (fun x : Eˣ => f x) (multHaar E) ↔ Integrable (nfib E f) (multHaar F)) ∧
      ∫ x : Eˣ, f x ∂multHaar E = κ * ∫ a : Fˣ, nfib E f a ∂multHaar F

end WF

section SP

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

abbrev muS (χ : AddChar F Circle) : Measure (F × F) := (selfDualMeasure χ).prod (selfDualMeasure χ)

abbrev rWS (χ : AddChar F Circle) : Matrix (Fin 2) (Fin 2) F → (F × F → ℂ) → F × F → ℂ := rWm χ swapE (muS χ) 1

def piS (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (h : GL (Fin 2) F) (Φ : F × F → ℂ) (x : F × F) : ℂ :=
  ((c₁ (GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det h) (1 / 2) *
    rW χ swapE (muS χ) 1 (h.val 0 0 / (h.val).det) (h.val 0 1) (h.val 1 0 / (h.val).det) (h.val 1 1)
      (fun y => Φ (y * ((h.val).det, 1))) x

end SP

def ForEF (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E],
    AddChar F Circle → (E ≃ₐ[F] E) → (Fˣ →* ℂˣ) → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] [CharZero F] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 →
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E]
      [BorelSpace E] [Algebra F E], Module.finrank F E = 2 → Continuous (algebraMap F E) →
    ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ η : Fˣ →* ℂˣ, (∀ a, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → P F E χ σ η

def ForES (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] [CharZero F], AddChar F Circle → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] [CharZero F] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → P F χ

end Ad3.K.GL2LocalData
end
end

section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.K.GL2LocalData

def WSB : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Φ ∈ SBE E,
  rWE E χ σ η g Φ ∈ SBE E ∧ ∀ c : Eˣ →* ℂˣ, Φ ∈ SBc F E c → rWE E χ σ η g Φ ∈ SBc F E c

def WPsi : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (c : Eˣ →* ℂˣ) (Φ : E → ℂ) (x : F) (g : GL (Fin 2) F),
  WcE E χ σ η c Φ (uni2 x * g) = (χ x : ℂ) * WcE E χ σ η c Φ g

def WChoice : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (c : Eˣ →* ℂˣ), ∀ Φ ∈ SBc F E c, ∀ (g : GL (Fin 2) F) (t : Eˣ),
  Algebra.norm F (t : E) = (g.val).det → WcE E χ σ η c Φ g = ((c t : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
    rW χ σ (muE E χ) (lamE E χ η) (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1)
      (fun y => Φ (y * (t : E))) 1

def WGaussEx : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∃ γ : ℂ, ∀ (a : Fˣ), ∀ Φ ∈ SBE E,
  ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ =
    γ * nsg E (a : F) * (((modulus (a : F) : ℝ)⁻¹ : ℝ) : ℂ) * ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ

def WGaussLam : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ γ : ℂ, (∀ (a : Fˣ), ∀ Φ ∈ SBE E,
  ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ =
    γ * nsg E (a : F) * (((modulus (a : F) : ℝ)⁻¹ : ℝ) : ℂ) * ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) →
  γ = lamE E χ η

def WRepN : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ (b : F), ∀ Φ ∈ SBE E,
  rWE E χ σ η (g * !![1, b; 0, 1]) Φ = rWE E χ σ η g (rWE E χ σ η !![1, b; 0, 1] Φ)

def WRepM : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ (s : Fˣ), ∀ Φ ∈ SBE E,
  rWE E χ σ η (g * !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)]) Φ = rWE E χ σ η g (rWE E χ σ η !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)] Φ)

def WRepW : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Φ ∈ SBE E,
  rWE E χ σ η (g * !![0, 1; -1, 0]) Φ = rWE E χ σ η g (rWE E χ σ η !![0, 1; -1, 0] Φ)

def WRep : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ g h : Matrix (Fin 2) (Fin 2) F, g.det = 1 → h.det = 1 → ∀ Φ ∈ SBE E,
  rWE E χ σ η (g * h) Φ = rWE E χ σ η g (rWE E χ σ η h Φ)

def WDiagT : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ (t : Eˣ), ∀ Φ ∈ SBE E,
  (fun y => rWE E χ σ η g Φ (y * (t : E))) = rWE E χ σ η (cjA (Algebra.norm F (t : E)) g) (fun y => Φ (y * (t : E)))

def WPiRep : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (c : Eˣ →* ℂˣ), ∀ Φ ∈ SBc F E c, ∀ g h : GL (Fin 2) F,
  (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) →
    WcE E χ σ η c Φ (g * h) = WcE E χ σ η c (piE E χ σ η c h Φ) g ∧ piE E χ σ η c h Φ ∈ SBc F E c

def WCen : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (c : Eˣ →* ℂˣ), ∀ Φ ∈ SBc F E c, ∀ (a : Fˣ) (g : GL (Fin 2) F),
  WcE E χ σ η c Φ (dg2 a a * g) = (((resF (F := F) c * η) a : ℂˣ) : ℂ) * WcE E χ σ η c Φ g

def WSmooth : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ Φ ∈ SBc F E c,
  ∃ U : OpenSubgroup (GL (Fin 2) F), ∀ g, ∀ u ∈ U, WcE E χ σ η c Φ (g * u) = WcE E χ σ η c Φ g

def WBound : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ Φ ∈ SBc F E c, ∀ h₀ : GL (Fin 2) F, ∃ C B : ℝ,
  ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
    ‖WcE E χ σ η c Φ (dg2 a 1 * k * h₀)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) ∧
      (WcE E χ σ η c Φ (dg2 a 1 * k * h₀) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)

def WMod : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ x : E, (modulus x : ℝ) = modulus (Algebra.norm F x)

def WFib : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∃ κ : ℝ, 0 < κ ∧ FibProp F E κ

def WZ : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ κ : ℝ, FibProp F E κ → ∀ (c : Eˣ →* ℂˣ) (μ : Fˣ →* ℂˣ), IsUnit1 c → IsUnit1 μ →
  ∀ Φ ∈ SBc F E c, ∀ s : ℂ, 0 < s.re →
    Integrable (fun a => WcE E χ σ η c Φ (dg2 a 1) * ((μ a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (multHaar F) ∧
      κ * zJ (WcE E χ σ η c Φ) μ s = localZeta Φ (c * viaN μ) s

def WZd : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ κ : ℝ, FibProp F E κ → ∀ (c : Eˣ →* ℂˣ) (μ : Fˣ →* ℂˣ), IsUnit1 c → IsUnit1 μ →
  ∀ Φ ∈ SBc F E c, ∀ s : ℂ, s.re < 1 →
    Integrable (fun a => WcE E χ σ η c Φ (dg2 a 1 * w0) * ((((resF (F := F) c * η) a * μ a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s))
        (multHaar F) ∧
      κ * zJ' (WcE E χ σ η c Φ) (resF (F := F) c * η) μ s =
        lamE E χ η * localZeta (localFourier (muE E χ) (chE E χ) Φ) (c * viaN μ)⁻¹ (1 - s)

def WFeTr : Prop := ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ Φ ∈ SBc F E c, ∀ h₀ : GL (Fin 2) F,
  ∀ μ : Fˣ →* ℂˣ, IsUnit1 μ → ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (fun a => WcE E χ σ η c Φ (dg2 a 1 * w0 * h₀) * ((((resF (F := F) c * η) a * μ a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s))
        (multHaar F) ∧
    Integrable (fun a => WcE E χ σ η c Φ (dg2 a 1 * h₀) * ((μ a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (multHaar F) ∧
    ∫ a, WcE E χ σ η c Φ (dg2 a 1 * w0 * h₀) * ((((resF (F := F) c * η) a * μ a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) ∂multHaar F =
      lamE E χ η * gam (chE E χ) (c * viaN μ) s *
        ∫ a, WcE E χ σ η c Φ (dg2 a 1 * h₀) * ((μ a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F

def SGauss : Prop := ForES fun F _ _ _ _ _ _ _ χ => ∀ (a : Fˣ), ∀ Φ ∈ SBE (F × F),
  ∫ u, (χ ((a : F) * (u.1 * u.2)) : ℂ) * FTs χ swapE (muS χ) Φ u ∂muS χ =
    (((modulus (a : F) : ℝ)⁻¹ : ℝ) : ℂ) * ∫ z, (χ (-(z.1 * z.2) / a) : ℂ) * Φ z ∂muS χ

def SRep : Prop := ForES fun F _ _ _ _ _ _ _ χ => ∀ g h : Matrix (Fin 2) (Fin 2) F, g.det = 1 → h.det = 1 → ∀ Φ ∈ SBE (F × F),
  rWS χ h Φ ∈ SBE (F × F) ∧ rWS χ (g * h) Φ = rWS χ g (rWS χ h Φ)

def SPsi : Prop := ForES fun F _ _ _ _ _ _ _ χ => ∀ (c₁ c₂ : Fˣ →* ℂˣ) (Φ : F × F → ℂ) (x : F) (g : GL (Fin 2) F),
  WcS χ c₁ c₂ Φ (uni2 x * g) = (χ x : ℂ) * WcS χ c₁ c₂ Φ g

def SPiRep : Prop := ForES fun F _ _ _ _ _ _ _ χ => ∀ (c₁ c₂ : Fˣ →* ℂˣ), IsUnit1 c₁ → IsUnit1 c₂ → ∀ Φ ∈ SBE (F × F), ∀ g h : GL (Fin 2) F,
  WcS χ c₁ c₂ Φ (g * h) = WcS χ c₁ c₂ (piS χ c₁ h Φ) g ∧ piS χ c₁ h Φ ∈ SBE (F × F)

def SCen : Prop := ForES fun F _ _ _ _ _ _ _ χ => ∀ (c₁ c₂ : Fˣ →* ℂˣ), IsUnit1 c₁ → IsUnit1 c₂ → ∀ Φ ∈ SBE (F × F), ∀ (a : Fˣ) (g : GL (Fin 2) F),
  WcS χ c₁ c₂ Φ (dg2 a a * g) = ((c₁ a * c₂ a : ℂˣ) : ℂ) * WcS χ c₁ c₂ Φ g

def SSmooth : Prop := ForES fun F _ _ _ _ _ _ _ χ => ∀ (c₁ c₂ : Fˣ →* ℂˣ), IsUnit1 c₁ → IsUnit1 c₂ → ∀ Φ ∈ SBE (F × F),
  ∃ U : OpenSubgroup (GL (Fin 2) F), ∀ g, ∀ u ∈ U, WcS χ c₁ c₂ Φ (g * u) = WcS χ c₁ c₂ Φ g

def SBound : Prop := ForES fun F _ _ _ _ _ _ _ χ => ∀ (c₁ c₂ : Fˣ →* ℂˣ), IsUnit1 c₁ → IsUnit1 c₂ → ∀ Φ ∈ SBE (F × F), ∀ ε : ℝ, 0 < ε →
  ∃ C B : ℝ, ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
    ‖WcS χ c₁ c₂ Φ (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧
      (WcS χ c₁ c₂ Φ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)

def SFe0 : Prop := ForES fun F _ _ _ _ _ _ _ χ => ∀ (c₁ c₂ : Fˣ →* ℂˣ), IsUnit1 c₁ → IsUnit1 c₂ → ∀ Φ ∈ SBE (F × F),
  ∀ μ : Fˣ →* ℂˣ, IsUnit1 μ → ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (fun a => WcS χ c₁ c₂ Φ (dg2 a 1 * w0) * (((c₁ a * c₂ a * μ a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s))
        (multHaar F) ∧
    Integrable (fun a => WcS χ c₁ c₂ Φ (dg2 a 1) * ((μ a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (multHaar F) ∧
    ∫ a, WcS χ c₁ c₂ Φ (dg2 a 1 * w0) * (((c₁ a * c₂ a * μ a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) ∂multHaar F =
      gam χ (c₁ * μ) s * gam χ (c₂ * μ) s * ∫ a, WcS χ c₁ c₂ Φ (dg2 a 1) * ((μ a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F

end Ad3.K.GL2LocalData
end
end
