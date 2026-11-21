import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.IsGoodV

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def LocData (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)) : Prop :=
  IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧
  SelfDual μ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) ∧
  SelfDual ν (fun S S' => psiV F ψ v (pairHerm (Fv F v) σ n S S'))

def IsGramFib {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n))
    (fib : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)) : Prop :=
  IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | FreeT (F := F) (E := E) (Fv F v) X} ν Set.univ fib

def FreeFramesOpenConull : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (M n : ℕ), n ≤ M →
    (∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure →
      IsOpen {X : Fin n → Fin M → Fv F v ⊗[F] E | FreeT (F := F) (E := E) (Fv F v) X} ∧ μ {X | ¬ FreeT (F := F) (E := E) (Fv F v) X} = 0) ∧
    ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
      IsOpen {X : Fin n → Fin M → Ainf F ⊗[F] E | FreeT (F := F) (E := E) (Ainf F) X} ∧ μ {X | ¬ FreeT (F := F) (E := E) (Ainf F) X} = 0

def GramMapFibreFamily : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)),
    LocData F E σ M n J ψ v μ ν → n ≤ M →
    ∃ fib, IsGramFib σ J v μ ν fib ∧
      (∀ (S : HermR (Fv F v) σ n) (U : Set (Fin n → Fin M → Fv F v ⊗[F] E)), IsOpen U →
        (U ∩ XT (Fv F v) σ J S.1).Nonempty → 0 < fib S U) ∧
      ∀ S : HermR (Fv F v) σ n, IsUnit S.1.det →
        ∀ K, IsCompact K → fib S K < ⊤

def GramFibreFamilyUnique : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)),
    LocData F E σ M n J ψ v μ ν → n ≤ M →
    ∀ fib fib', IsGramFib σ J v μ ν fib → IsGramFib σ J v μ ν fib' → fib = fib'

def HaarScalingGramMap : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)),
    LocData F E σ M n J ψ v μ ν → n ≤ M → ∀ fib, IsGramFib σ J v μ ν fib →
    (∀ (g : GL (Fin n) (Fv F v ⊗[F] E)) (c c' : ℝ≥0∞),
      (∀ A, MeasurableSet A → μ ((fun X => tupMul (Fv F v) X (g⁻¹ : GL (Fin n) _).val) ⁻¹' A) = c * μ A) →
      (∀ A : Set (HermR (Fv F v) σ n), MeasurableSet A →
        ν {S | ∃ S' ∈ A, S.1 = starT (Fv F v) σ g.val * S'.1 * g.val} = c' * ν A) →
      c' ≠ 0 → c' ≠ ⊤ →
      ∀ (S S' : HermR (Fv F v) σ n), S'.1 = starT (Fv F v) σ g.val * S.1 * g.val →
        ∀ φ : (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞, Measurable φ →
          ∫⁻ X, φ X ∂(fib S') = c / c' * ∫⁻ X, φ (tupMul (Fv F v) X g.val) ∂(fib S)) ∧
    ∀ (h : HA (Fv F v) σ J) (S : HermR (Fv F v) σ n), (fib S).map (fun X => h • X) = fib S

def WittTransitivityFreeFrames : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (∀ X X' : Fin n → Fin M → E, LinearIndependent E X → LinearIndependent E X' →
      gramE σ J X = gramE σ J X' →
      ∃ g : GL (Fin M) E, g ∈ Formalism.UG.UJ (σ : E →+* E) J ∧ ∀ a, (g : Matrix (Fin M) (Fin M) E).mulVec (X a) = X' a) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (X X' : Fin n → Fin M → Fv F v ⊗[F] E), FreeT (F := F) (E := E) (Fv F v) X →
      FreeT (F := F) (E := E) (Fv F v) X' → gramR (Fv F v) σ J X = gramR (Fv F v) σ J X' →
      ∃ h : HA (Fv F v) σ J, h • X = X'

def GoodPlaceOrthonormalLattice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), IsGoodV b σ J v (psiV F ψ v) →
    (∃ e : Fin M → Fin M → Fv F v ⊗[F] E, (∀ i, e i ∈ latW b v) ∧
      (∀ i j, hR (Fv F v) σ J (e i) (e j) = if i = j then 1 else 0) ∧
      ∀ y ∈ latW (M := M) b v, ∃ c : Fin M → Fv F v ⊗[F] E, (∀ i, c i ∈ latE b v) ∧ y = ∑ i, c i • e i) ∧
    (∀ x ∈ latW (M := M) b v, (Valued.v (qR (Fv F v) σ J x)) = 1 →
      ∃ y ∈ latW (M := M) b v, hR (Fv F v) σ J x y = 1) ∧
    ∀ β : Fv F v, (Valued.v β = 1 ∨ β = 0) →
      ∀ x ∈ latW (M := M) b v, ∀ x' ∈ latW (M := M) b v,
        (∃ y ∈ latW (M := M) b v, hR (Fv F v) σ J x y = 1) → (∃ y ∈ latW (M := M) b v, hR (Fv F v) σ J x' y = 1) →
        qR (Fv F v) σ J x = β → qR (Fv F v) σ J x' = β →
        ∃ h : HA (Fv F v) σ J, (∀ y, y ∈ latW (M := M) b v ↔ (HA.mat (Fv F v) σ J h : Matrix (Fin M) (Fin M) _).mulVec y ∈ latW b v) ∧
          (HA.mat (Fv F v) σ J h : Matrix (Fin M) (Fin M) _).mulVec x = x'

def FundamentalDomainPigeonhole : Prop :=
  ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]
    (Λ : AddSubgroup G) [Countable Λ] (D : Set G), IsAddFundamentalDomain Λ D μ → μ D = 1 →
    ∀ Ω₀ : Set G, MeasurableSet Ω₀ → 1 < μ Ω₀ → ∃ l ∈ Λ, l ≠ 0 ∧ ∃ x ∈ Ω₀, ∃ y ∈ Ω₀, l = x - y

end PI.GramFibrationFormulas
end
end

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def FinVolH (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Prop :=
  ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure →
    ∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ ∧ μ 𝓕 < ⊤

def FinVolStab (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) : Prop :=
  ∀ μ' : Measure (Hstab (AF F) σ J x), μ'.IsHaarMeasure →
    ∃ 𝓕', IsFundamentalDomain (HstabFin (AF F) σ J x) 𝓕' μ' ∧ μ' 𝓕' < ⊤

def X0int {d M : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin M → Fv F v ⊗[F] E) :=
  {y | y ∈ latW b v ∧ (∃ z ∈ latW (M := M) b v, hR (Fv F v) σ J y z = 1) ∧ qR (Fv F v) σ J y = 0}

def AnisotropicOrbitSurjective : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (x : Fin 1 → Fin M → E) (β : F), β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
      let X := {y : Fin 1 → Fin M → AF F ⊗[F] E | qR (AF F) σ J (y 0) = algebraMap F (AF F) β}
      (∀ y ∈ X, ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) ∧
      Continuous (fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) x) ∧
      ∀ U : Set (HA (AF F) σ J), IsOpen U →
        ∃ O, IsOpen O ∧ (fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) x) '' U = O ∩ X

def IsotropicOrbitSurjective : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ x : Fin 1 → Fin M → E, x 0 ≠ 0 → hE σ J (x 0) (x 0) = 0 →
      let Xv := fun (v : HeightOneSpectrum (𝓞 F)) (y : Fin 1 → Fin M → AF F ⊗[F] E) => projV v (projFin y)
      let X0 := {y : Fin 1 → Fin M → AF F ⊗[F] E | qR (AF F) σ J (y 0) = 0 ∧
        FreeT (F := F) (E := E) (Ainf F) (projInf y) ∧ (∀ v, FreeT (F := F) (E := E) (Fv F v) (Xv v y)) ∧
        ∀ᶠ v in Filter.cofinite, Xv v y 0 ∈ X0int b σ J v}
      (∀ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x ∈ X0) ∧
      (∀ y ∈ X0, ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) ∧
      ∀ (U : Set (HA (AF F) σ J)) (g : HA (AF F) σ J), IsOpen U → g ∈ U →
        ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (Ui : Set (Fin 1 → Fin M → Ainf F ⊗[F] E))
          (Uv : ∀ v, Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsOpen Ui ∧ (∀ v ∈ S, IsOpen (Uv v)) ∧
          g • ratTup (F := F) (AF F) x ∈ {y | projInf y ∈ Ui ∧ ∀ v, (v ∈ S → Xv v y ∈ Uv v) ∧
            (v ∉ S → Xv v y 0 ∈ X0int b σ J v)} ∧
          {y ∈ X0 | projInf y ∈ Ui ∧ ∀ v, (v ∈ S → Xv v y ∈ Uv v) ∧ (v ∉ S → Xv v y 0 ∈ X0int b σ J v)} ⊆
            (fun h : HA (AF F) σ J => h • ratTup (F := F) (AF F) x) '' U

def UnitaryStabilizerQuotient : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant) ∧
    (∀ (x : Fin 1 → Fin M → E) (β : F), β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
      ∃ (M' : ℕ) (J' : Matrix (Fin M') (Fin M') E) (Ψ : Hstab (AF F) σ J x ≃ₜ* HA (AF F) σ J'),
        M' + 1 = M ∧ IsHermND σ J' ∧
        ∀ u, u ∈ HstabFin (AF F) σ J x ↔ Ψ u ∈ HFinIn (AF F) σ J') ∧
    ∀ x : Fin 1 → Fin M → E, x 0 ≠ 0 → hE σ J (x 0) (x 0) = 0 → 3 ≤ M →
      (∀ μ' : Measure (Hstab (AF F) σ J x), μ'.IsHaarMeasure → μ'.IsMulRightInvariant) ∧
      ((∀ (J₁ : Matrix (Fin (M - 2)) (Fin (M - 2)) E), IsHermND σ J₁ → FinVolH σ J₁) → FinVolStab σ J x)

def OrbitUnfoldingFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (x : Fin 1 → Fin M → E) (X : Set (Fin 1 → Fin M → E)) (gy : (Fin 1 → Fin M → E) → HA (AF F) σ J),
      (∀ y, y ∈ X ↔ ∃ g ∈ HFinIn (AF F) σ J, g • ratTup (F := F) (AF F) x = ratTup (F := F) (AF F) y) →
      (∀ y ∈ X, gy y ∈ HFinIn (AF F) σ J ∧ gy y • ratTup (F := F) (AF F) y = ratTup (F := F) (AF F) x) →
    ∀ (μ : Measure (HA (AF F) σ J)) (μ' : Measure (Hstab (AF F) σ J x))
      (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) 𝓕 𝓕',
      μ.IsHaarMeasure → μ.IsMulRightInvariant → μ'.IsHaarMeasure → μ'.IsMulRightInvariant →
      IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → IsFundamentalDomain (HstabFin (AF F) σ J x) 𝓕' μ' →
      Formalism.MainNotions.StandardLattice.Carries F E σ M J x μ μ' ν →
      ∀ (s : (Fin 1 → Fin M → AF F ⊗[F] E) → HA (AF F) σ J),
        (∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) → s y • ratTup (F := F) (AF F) x = y) →
      ∀ φ : HA (AF F) σ J → ℝ≥0∞, Measurable φ →
        (∀ u ∈ HstabFin (AF F) σ J x, ∀ h, φ ((u : HA (AF F) σ J) * h) = φ h) →
        ∫⁻ h in 𝓕, ∑' y : X, φ (gy y * h) ∂μ =
          ∫⁻ y, ∫⁻ u in 𝓕', φ ((u : HA (AF F) σ J) * (s y)⁻¹) ∂μ' ∂ν

end PI.GramFibrationFormulas
end
end
