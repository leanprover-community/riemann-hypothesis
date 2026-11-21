import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.AnisotropicOrbitSurjective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.IsGoodV

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def GeneralLinearUnimodular : Prop :=
  ∀ (K : Type) [NontriviallyNormedField K] [LocallyCompactSpace K] [SecondCountableTopology K] (M : ℕ),
    letI : MeasurableSpace (GL (Fin M) K) := borel _
    ∀ μ : Measure (GL (Fin M) K), μ.IsHaarMeasure → μ.IsMulRightInvariant

def WeilUnimodularityCriterion : Prop :=
  ∀ (L X : Type) [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L] [T2Space L]
    [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] [MulAction L X] [ContinuousSMul L X] (x : X),
    (∀ μ : Measure L, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
    (∀ y : X, ∃ g : L, g • x = y) → IsOpenMap (fun g : L => g • x) →
    (∃ m : Measure X, m ≠ 0 ∧ (∀ K, IsCompact K → m K < ⊤) ∧ ∀ g : L, m.map (fun y => g • y) = m) →
    ∀ ν : Measure (MulAction.stabilizer L x), ν.IsHaarMeasure → ν.IsMulRightInvariant

def LocalUnitaryUnimodular : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (HA (Fv F v) σ J)), μ.IsHaarMeasure → μ.IsMulRightInvariant) ∧
    ∀ μ : Measure (HA (Ainf F) σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant

def AdelicUnitaryUnimodular : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant

def IsGramFibInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (ν : Measure (HermR (Ainf F) σ n)) (fib : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)) : Prop :=
  IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val {X | FreeT (F := F) (E := E) (Ainf F) X} ν Set.univ fib

def ArchimedeanGramFibreFamily : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → n ≤ M →
    SelfDual μ (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) →
    SelfDual ν (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ n S S')) →
    (∃ fib, IsGramFibInf σ J μ ν fib ∧
      (∀ (S : HermR (Ainf F) σ n) (U : Set (Fin n → Fin M → Ainf F ⊗[F] E)), IsOpen U →
        (U ∩ XT (Ainf F) σ J S.1).Nonempty → 0 < fib S U) ∧
      ∀ S : HermR (Ainf F) σ n, IsUnit S.1.det → ∀ K, IsCompact K → fib S K < ⊤) ∧
    ∀ fib fib', IsGramFibInf σ J μ ν fib → IsGramFibInf σ J μ ν fib' → fib = fib'

def ArchimedeanHaarScaling : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → n ≤ M →
    SelfDual μ (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) →
    SelfDual ν (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ n S S')) →
    ∀ fib, IsGramFibInf σ J μ ν fib →
    (∀ (g : GL (Fin n) (Ainf F ⊗[F] E)) (c c' : ℝ≥0∞),
      (∀ A, MeasurableSet A → μ ((fun X => tupMul (Ainf F) X (g⁻¹ : GL (Fin n) _).val) ⁻¹' A) = c * μ A) →
      (∀ A : Set (HermR (Ainf F) σ n), MeasurableSet A →
        ν {S | ∃ S' ∈ A, S.1 = starT (Ainf F) σ g.val * S'.1 * g.val} = c' * ν A) →
      c' ≠ 0 → c' ≠ ⊤ →
      ∀ (S S' : HermR (Ainf F) σ n), S'.1 = starT (Ainf F) σ g.val * S.1 * g.val →
        ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞, Measurable φ →
          ∫⁻ X, φ X ∂(fib S') = c / c' * ∫⁻ X, φ (tupMul (Ainf F) X g.val) ∂(fib S)) ∧
    ∀ (h : HA (Ainf F) σ J) (S : HermR (Ainf F) σ n), (fib S).map (fun X => h • X) = fib S

def RealGaussianAnyCharacter : Prop :=
  ∀ (M : ℕ) (η : Fin (2 * M) → ℝ) (α : ℝ), (∀ l, η l = 1 ∨ η l = -1) → α ≠ 0 →
    let q := fun u : Fin (2 * M) → ℝ => ∑ l, η l * u l ^ 2
    let qp := fun u : Fin (2 * M) → ℝ => ∑ l, u l ^ 2
    let B := fun u u' : Fin (2 * M) → ℝ => 2 * ∑ l, η l * u l * u' l
    let φ := fun (τ : ℂ) (u : Fin (2 * M) → ℝ) =>
      Complex.exp (2 * Real.pi * Complex.I * α * τ.re * q u - 2 * Real.pi * |α| * τ.im * qp u)
    ∀ τ : ℂ, 0 < τ.im → ∃ c : ℂ, c ≠ 0 ∧ ∀ u' : Fin (2 * M) → ℝ,
      ((2 * |α|) ^ M : ℝ) * ∫ u, φ τ u * Complex.exp (2 * Real.pi * Complex.I * α * B u u') = c * φ (-1 / τ) u'

end PI.GramFibrationFormulas
end
end

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsQFib (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v))
    (fq : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) : Prop :=
  IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id {X | X 0 ≠ 0} ν Set.univ fq

def IsQFibInf (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (Ainf F))
    (fq : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) : Prop :=
  IsFibreFamily μ (fun X => qR (Ainf F) σ J (X 0)) id {X | FreeT (F := F) (E := E) (Ainf F) X} ν Set.univ fq

def resCard (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)

def modF {v : HeightOneSpectrum (𝓞 F)} (ν : Measure (Fv F v)) (a : Fv F v) : ℝ≥0∞ :=
  ν ((fun t => a * t) '' (v.adicCompletionIntegers F : Set (Fv F v))) / ν (v.adicCompletionIntegers F)

def modT {d M n : ℕ} (b : Module.Basis (Fin d) F E) {v : HeightOneSpectrum (𝓞 F)}
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (a : Fv F v) : ℝ≥0∞ :=
  μ ((fun X => a • X) '' latV b v) / μ (latV b v)

def FstarT {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] (χ : R → ℂ) (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (φ : (Fin 1 → Fin M → R ⊗[F] E) → ℂ)
    (b : R) : ℂ :=
  ∫ X, φ X * χ (b * qR R σ J (X 0)) ∂μ

def FiniteFibreMeasureFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → 2 ≤ M →
    SelfDual μ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) → SelfDual ν (fun s t => psiV F ψ v (s * t)) →
    (∃ fq, IsQFib σ J v μ ν fq) ∧
    ∀ fq, IsQFib σ J v μ ν fq →
      (∀ φ, IsSB φ →
        Continuous (fun β => ∫ X, φ X ∂(fq β)) ∧
        IsContDensity μ (fun X => qR (Fv F v) σ J (X 0)) id ν φ (fun β => ∫ X, φ X ∂(fq β)) ∧
        (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ β, ∫⁻ X, ‖φ X‖ₑ ∂(fq β) ≤ C) ∧
        ∀ β, ∫ X, φ X ∂(fq β) =
          ∫ s, FstarT (psiV F ψ v) σ J μ φ s * psiV F ψ v (-(s * β)) ∂ν) ∧
      (∀ (a : Fv F v), a ≠ 0 → ∀ (φ : (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φ → ∀ β,
        ∫⁻ X, φ (a • X) ∂(fq β) = modF ν a ^ 2 / modT b μ a * ∫⁻ X, φ X ∂(fq (a ^ 2 * β))) ∧
      (IsGoodV b σ J v (psiV F ψ v) → 3 ≤ M →
        (∀ β ∈ v.adicCompletionIntegers F,
          ‖∫ X, (latV (n := 1) (M := M) b v).indicator (fun _ => (1 : ℂ)) X ∂(fq β) - 1‖ ≤ 2 * (resCard v : ℝ) ^ (1 - (M : ℤ))) ∧
        ∀ β ∉ v.adicCompletionIntegers F, ∫ X, (latV (n := 1) (M := M) b v).indicator (fun _ => (1 : ℂ)) X ∂(fq β) = 0)

def ArchimedeanFibreFamily : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (Ainf F)),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → 2 ≤ M →
    SelfDual μ (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) → SelfDual ν (fun s t => psiInf F ψ (s * t)) →
    (∃ fq, IsQFibInf σ J μ ν fq) ∧
    ∀ fq, IsQFibInf σ J μ ν fq →
      (∀ φ, Continuous φ → RapidDecay b φ →
        Continuous (fun β => ∫ X, φ X ∂(fq β)) ∧
        IsContDensity μ (fun X => qR (Ainf F) σ J (X 0)) id ν φ (fun β => ∫ X, φ X ∂(fq β)) ∧
        ∀ k : ℕ, ∃ C : ℝ, ∀ β : Ainf F, (1 + ‖β‖) ^ k * (∫⁻ X, ‖φ X‖ₑ ∂(fq β)).toReal ≤ C ∧
          ∫⁻ X, ‖φ X‖ₑ ∂(fq β) < ⊤) ∧
      ∀ (a a' : Ainf F), a * a' = 1 → ∀ (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞), Measurable φ → ∀ β,
        ∫⁻ X, φ (a • X) ∂(fq β) =
          ENNReal.ofReal (∏ w, ‖a w‖ ^ (2 - 2 * (M : ℝ))) * ∫⁻ X, φ X ∂(fq (a ^ 2 * β))

def GlobalDensityProductFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → 3 ≤ M →
    ∀ (μi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (νi : Measure (Ainf F))
      (μv : ∀ v, Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v, Measure (Fv F v)),
      SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) → SelfDual νi (fun s t => psiInf F ψ (s * t)) →
      (∀ v, SelfDual (μv v) (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y))) →
      (∀ v, SelfDual (νv v) (fun s t => psiV F ψ v (s * t))) →
    ∀ (fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (fv : ∀ v, Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
      IsQFibInf σ J μi νi fi → (∀ v, IsQFib σ J v (μv v) (νv v) (fv v)) →
    ∀ β : F, ∃ ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E),
      (β ≠ 0 → Formalism.MainNotions.StandardLattice.IsDxDq F E σ M J ψ β ν) ∧
      (∀ g : HA (AF F) σ J, ν.map (fun X => g • X) = ν) ∧
      (∀ K, IsCompact K → ν K < ⊤) ∧
      (β = 0 → ν {X | ¬ (qR (AF F) σ J (X 0) = 0 ∧ FreeT (F := F) (E := E) (Ainf F) (projInf X) ∧
        (∀ v, FreeT (F := F) (E := E) (Fv F v) (projV v (projFin X))) ∧
        ∀ᶠ v in Filter.cofinite, projV v (projFin X) 0 ∈ X0int b σ J v)} = 0) ∧
      ∀ (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
        (Φv : ∀ v, (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞),
        Measurable Φi → (∀ v, Measurable (Φv v)) →
        (∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) →
        (∀ X, Φ X = Φi (projInf X) * ∏ᶠ v, Φv v (projV v (projFin X))) →
        ∫⁻ X, Φ X ∂ν = (∫⁻ X, Φi X ∂(fi (algebraMap F (Ainf F) β))) *
          ∏' v, ∫⁻ X, Φv v X ∂(fv v (algebraMap F (Fv F v) β))

def DensityEulerProductBound : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → 3 ≤ M →
    ∀ (μi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (νi : Measure (Ainf F))
      (μv : ∀ v, Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v, Measure (Fv F v)),
      SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) → SelfDual νi (fun s t => psiInf F ψ (s * t)) →
      (∀ v, SelfDual (μv v) (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y))) →
      (∀ v, SelfDual (νv v) (fun s t => psiV F ψ v (s * t))) →
    ∀ (fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (fv : ∀ v, Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
      IsQFibInf σ J μi νi fi → (∀ v, IsQFib σ J v (μv v) (νv v) (fv v)) →
    ∀ (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ) (Φv : ∀ v, (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φi → RapidDecay b Φi → (∀ v, IsSB (Φv v)) →
      (∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) →
      (∃ C : ℝ, ∀ s : Ainf F, ‖FstarT (psiInf F ψ) σ J μi Φi s‖ ≤ C * ∏ w, (max 1 ‖s w‖) ^ (-(M : ℝ))) →
      let Fst := fun y : AF F => FstarT (psiInf F ψ) σ J μi Φi (fstA F y) *
        ∏' v, FstarT (psiV F ψ v) σ J (μv v) (Φv v) (evalV F v (sndA F y))
      let Fd := fun β : F => (∫ X, Φi X ∂(fi (algebraMap F (Ainf F) β))) *
        ∏' v, ∫ X, Φv v X ∂(fv v (algebraMap F (Fv F v) β))
      ∀ y : AF F, Summable (fun c : F => ‖Fst (algebraMap F (AF F) c + y)‖) ∧
        Summable (fun β : F => ‖Fd β‖) ∧
        ∑' c : F, Fst (algebraMap F (AF F) c + y) = ∑' β : F, Fd β * ψ (algebraMap F (AF F) β * y)

end PI.GramFibrationFormulas
end
end

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def IsotropicLatticeCount : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    3 ≤ M → ∀ L' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E),
    (∀ v, IsCompact (L' v) ∧ IsOpen (L' v) ∧ 0 ∈ L' v ∧ (∀ x ∈ L' v, ∀ y ∈ L' v, x + y ∈ L' v) ∧
      ∀ x ∈ L' v, -x ∈ L' v) →
    (∀ᶠ v in Filter.cofinite, L' v = latV b v) →
    ∀ (μ : Measure (HA (AF F) σ J)) 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
      let N := fun R : ℝ => ∫⁻ h in 𝓕, ∑' x : (Fin 1 → Fin M → E),
        {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧
          (∀ v, projV v (projFin (h⁻¹ • ratTup (F := F) (AF F) x)) ∈ L' v) ∧
          sizeTup b (projInf (h⁻¹ • ratTup (F := F) (AF F) x)) ≤ R}.indicator 1 x ∂μ
      let dF := Module.finrank ℚ F
      (∀ R, N R < ⊤) ∧
      (∀ r R : ℝ, 0 < r → r ≤ R → N R ≤ ENNReal.ofReal ((5 * R / r) ^ (2 * M * dF)) * (μ 𝓕 + N r)) ∧
      ∃ r₀ C : ℝ, 0 < r₀ ∧ ∀ R : ℝ, 0 < R → R ≤ r₀ → N R ≤ ENNReal.ofReal (C * R ^ ((2 * M - 2) * dF))

def HermitianDilationFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ β : F, β ≠ 0 →
    ∀ ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E), Formalism.MainNotions.StandardLattice.IsDxDq F E σ M J ψ β ν →
    ∀ (μ : Measure (HA (AF F) σ J)) 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
    ∀ Ψ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Ψ →
      meanL μ 𝓕 (fun h => ∑' x : {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧ hE σ J (x 0) (x 0) = algebraMap F E β},
        Ψ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))) = ∫⁻ y, Ψ y ∂ν

def HermitianDiagonalization : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), (∀ a c, σ (T c a) = T a c) → T.det ≠ 0 →
    ∃ (g : GL (Fin n) E) (t : Fin n → F), (∀ i, t i ≠ 0) ∧
      ((g : Matrix (Fin n) (Fin n) E).map σ).transpose * T * (g : Matrix (Fin n) (Fin n) E) =
        Matrix.diagonal (fun i => algebraMap F E (t i))

def LocalInductionFinitePlace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M M' n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → M' + 1 = M → n + 1 ≤ M →
    ∀ (x₀ : Fin M → E) (t₁ : F) (P₀ : Matrix (Fin M) (Fin M') E), t₁ ≠ 0 →
      hE σ J x₀ x₀ = algebraMap F E t₁ → (∀ j, hE σ J x₀ (fun i => P₀ i j) = 0) →
      LinearIndependent E (fun j i => P₀ i j) →
    let J' := (P₀.map σ).transpose * J * P₀
    let P₀v := P₀.map (inclR (F := F) (Fv F v))
    ∀ (μ : Measure (Fin (n + 1) → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (n + 1)))
      (μ' : Measure (Fin n → Fin M' → Fv F v ⊗[F] E)) (ν' : Measure (HermR (Fv F v) σ n))
      (μ₁ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν₁ : Measure (Fv F v)),
      LocData F E σ M (n + 1) J ψ v μ ν → LocData F E σ M' n J' ψ v μ' ν' →
      SelfDual μ₁ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) → SelfDual ν₁ (fun s t => psiV F ψ v (s * t)) →
    ∀ fib fib' fq, IsGramFib σ J v μ ν fib → IsGramFib σ J' v μ' ν' fib' → IsQFib σ J v μ₁ ν₁ fq →
    ∀ s : (Fin 1 → Fin M → Fv F v ⊗[F] E) → HA (Fv F v) σ J, Measurable s →
      (∀ x, qR (Fv F v) σ J (x 0) = algebraMap F (Fv F v) t₁ →
        s x • (fun _ i => inclR (F := F) (Fv F v) (x₀ i)) = x) →
    ∀ (T : HermR (Fv F v) σ (n + 1)) (T' : HermR (Fv F v) σ n),
      (∀ a b : Fin n, T.1 a.succ b.succ = T'.1 a b) → T.1 0 0 = inclR (F := F) (Fv F v) (algebraMap F E t₁) →
      (∀ a : Fin n, T.1 0 a.succ = 0) →
    ∀ φ : (Fin (n + 1) → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞, Measurable φ →
      ∫⁻ X, φ X ∂(fib T) = (modF ν₁ (algebraMap F (Fv F v) t₁))⁻¹ ^ n *
        ∫⁻ x, ∫⁻ Y, φ (Fin.cons (x 0) (fun a =>
          (HA.mat (Fv F v) σ J (s x) : Matrix (Fin M) (Fin M) _).mulVec (P₀v.mulVec (Y a)))) ∂(fib' T') ∂(fq (algebraMap F (Fv F v) t₁))

def IsPureL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
    (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (Φv : ∀ v, (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞) : Prop :=
  Measurable Φi ∧ (∀ v, Measurable (Φv v)) ∧ (∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) ∧
    ∀ X, Φ X = Φi (projInf X) * ∏ᶠ v, Φv v (projV v (projFin X))

def SiegelWeilPureFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M n : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), T.det ≠ 0 →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∀ (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (νi : Measure (HermR (Ainf F) σ n))
      (μv : ∀ v, Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v, Measure (HermR (Fv F v) σ n)),
      SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) →
      SelfDual νi (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ n S S')) →
      (∀ v, LocData F E σ M n J ψ v (μv v) (νv v)) →
    ∀ (fi : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (fv : ∀ v, HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsGramFibInf σ J μi νi fi → (∀ v, IsGramFib σ J v (μv v) (νv v) (fv v)) →
    ∀ (μ : Measure (HA (AF F) σ J)) 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
    ∀ Φ Φi Φv, IsPureL b Φ Φi Φv →
      meanL μ 𝓕 (fun h => ∑' X : {X : Fin n → Fin M → E | gramE σ J X = T},
        Φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin n → Fin M → E))) =
        (∫⁻ X, Φi X ∂(fi (hermOf (Ainf F) σ T hT))) * ∏' v, ∫⁻ X, Φv v X ∂(fv v (hermOf (Fv F v) σ T hT))

def SchwartzBruhatConvergence : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M n : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    n ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), T.det ≠ 0 →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∀ (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (νi : Measure (HermR (Ainf F) σ n))
      (μv : ∀ v, Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v, Measure (HermR (Fv F v) σ n)),
      SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) →
      SelfDual νi (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ n S S')) →
      (∀ v, LocData F E σ M n J ψ v (μv v) (νv v)) →
    ∀ (fi : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (fv : ∀ v, HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsGramFibInf σ J μi νi fi → (∀ v, IsGramFib σ J v (μv v) (νv v) (fv v)) →
    ∀ (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φv : ∀ v, (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φi → RapidDecay b Φi → (∀ v, IsSB (Φv v)) →
      (∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) →
      IsContDensityOn μi (gramR (Ainf F) σ J) Subtype.val νi
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φi (fun S => ∫ X, Φi X ∂(fi S)) ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} (Φv v) (fun S => ∫ X, Φv v X ∂(fv v S))) ∧
      ∫⁻ X, ‖Φi X‖ₑ ∂(fi (hermOf (Ainf F) σ T hT)) < ⊤ ∧
      (∀ v, ∫⁻ X, ‖Φv v X‖ₑ ∂(fv v (hermOf (Fv F v) σ T hT)) < ⊤) ∧
      ∏' v, ∫⁻ X, ‖Φv v X‖ₑ ∂(fv v (hermOf (Fv F v) σ T hT)) < ⊤ ∧
      Multipliable (fun v => ∫ X, Φv v X ∂(fv v (hermOf (Fv F v) σ T hT)))

end PI.GramFibrationFormulas
end
end

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def LocalFieldInstances : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Module.finrank F E = 2 → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    (∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (Fv F v) ∧ SecondCountableTopology (Fv F v) ∧
      IsTopologicalRing (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧
      LocallyCompactSpace (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧
      BorelSpace (Fv F v ⊗[F] E)) ∧
    (IsTopologicalRing (Ainf F ⊗[F] E) ∧ T2Space (Ainf F ⊗[F] E) ∧ LocallyCompactSpace (Ainf F ⊗[F] E) ∧
      SecondCountableTopology (Ainf F ⊗[F] E) ∧ BorelSpace (Ainf F ⊗[F] E)) ∧
    (IsTopologicalRing (AF F ⊗[F] E) ∧ T2Space (AF F ⊗[F] E) ∧ LocallyCompactSpace (AF F ⊗[F] E) ∧
      SecondCountableTopology (AF F ⊗[F] E) ∧ BorelSpace (AF F ⊗[F] E)) ∧
    (IsTopologicalGroup (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) ∧ LocallyCompactSpace (HA (AF F) σ J) ∧
      SecondCountableTopology (HA (AF F) σ J) ∧ BorelSpace (HA (AF F) σ J))

def AdelicVectorDecomposition : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (d M n : ℕ) (b : Module.Basis (Fin d) F E),
    IsHomeomorph (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) ∧
    (∀ X : Fin n → Fin M → Af F ⊗[F] E, ∀ᶠ v in Filter.cofinite, projV v X ∈ latV b v) ∧
    Function.Injective (fun (X : Fin n → Fin M → Af F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)) => projV v X) ∧
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v, Set (Fin n → Fin M → Fv F v ⊗[F] E)),
      let P := {X : Fin n → Fin M → Af F ⊗[F] E |
        ∀ v, (v ∈ S → projV v X ∈ U v) ∧ (v ∉ S → projV v X ∈ latV b v)}
      ((∀ v ∈ S, IsOpen (U v)) → IsOpen P) ∧ ((∀ v ∈ S, IsCompact (U v)) → IsCompact P)

def RationalPointsLattice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    Countable (HFinIn (AF F) σ J) ∧ DiscreteTopology (HFinIn (AF F) σ J) ∧
    (∀ n : ℕ, DiscreteTopology (Set.range (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _)) ∧
      ∃ K : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact K ∧
        ∀ Y, ∃ X : Fin n → Fin M → E, Y - ratTup (F := F) (AF F) X ∈ K) ∧
    (∃ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure) ∧
    ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → ∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ

def GoodPlacesCofinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
      Set.Finite {v : HeightOneSpectrum (𝓞 F) | ¬ IsGoodV b σ J v (psiV F ψ v)}

def AdelicCharacterExistence : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    (∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ) ∧
    (∀ ψ ψ' : AddChar (AF F) ℂ, IsCharAF F ψ → IsCharAF F ψ' →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x)) ∧
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ y : AF F,
      (∀ a : F, ψ (algebraMap F (AF F) a * y) = 1) → ∃ c : F, y = algebraMap F (AF F) c

def SelfDualMeasuresExist : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ,
    (∃ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), SelfDual μ (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y))) ∧
    (∃ ν : Measure (HermR (Ainf F) σ n), SelfDual ν (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ n S S'))) ∧
    (∃ ν : Measure (Ainf F), SelfDual ν (fun s t => psiInf F ψ (s * t))) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      (∃ μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E), SelfDual μ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) ∧
        (IsGoodV b σ J v (psiV F ψ v) → μ (latV b v) = 1)) ∧
      (∃ ν : Measure (HermR (Fv F v) σ n), SelfDual ν (fun S S' => psiV F ψ v (pairHerm (Fv F v) σ n S S')) ∧
        (IsGoodV b σ J v (psiV F ψ v) →
          ν {S | ∀ a c, (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c ∈ latE b v} = 1)) ∧
      (∃ ν : Measure (Fv F v), SelfDual ν (fun s t => psiV F ψ v (s * t)) ∧
        (IsGoodV b σ J v (psiV F ψ v) → ν (v.adicCompletionIntegers F) = 1))

end PI.GramFibrationFormulas
end
end

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas
section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def B1 (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin M → Fv F v ⊗[F] E) : Fv F v :=
  Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J x y)

def rhoH {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y : Fin M → Fv F v ⊗[F] E) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) : (Fin M → Fv F v ⊗[F] E) → ℂ :=
  fun u => χ (B1 σ J v u y + B1 σ J v x y / 2) * φ (u + x)

def opU {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Fv F v) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) : (Fin M → Fv F v ⊗[F] E) → ℂ :=
  fun u => χ (b * qR (Fv F v) σ J u) * φ u

def modW {d M : ℕ} (b : Module.Basis (Fin d) F E) {v : HeightOneSpectrum (𝓞 F)}
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (a : Fv F v) : ℝ≥0∞ :=
  μ ((fun u => a • u) '' latW b v) / μ (latW b v)

def opD {d M : ℕ} (b : Module.Basis (Fin d) F E) {v : HeightOneSpectrum (𝓞 F)}
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (a : Fv F v) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) :
    (Fin M → Fv F v ⊗[F] E) → ℂ :=
  fun u => (((modW b μ a).toReal ^ (1 / 2 : ℝ) : ℝ) : ℂ) * φ (a • u)

def opF {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) : (Fin M → Fv F v ⊗[F] E) → ℂ :=
  fun u => ∫ s, φ s * χ (B1 σ J v s u) ∂μ

def Fstar {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) (b : Fv F v) : ℂ :=
  ∫ x, φ x * χ (b * qR (Fv F v) σ J x) ∂μ

def l2 {V : Type} [MeasurableSpace V] (μ : Measure V) (φ : V → ℂ) : ℝ := ∫ x, ‖φ x‖ ^ 2 ∂μ

def OmV {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (g : Matrix (Fin 2) (Fin 2) (Fv F v)) :
    Set (((Fin M → Fv F v ⊗[F] E) → ℂ) →ₗ[ℂ] ((Fin M → Fv F v ⊗[F] E) → ℂ)) :=
  {T | (∀ φ, IsSB φ → IsSB (T φ) ∧ l2 μ (T φ) = l2 μ φ) ∧
    ∀ x y φ, IsSB φ → rhoH χ σ J x y (T φ) = T (rhoH χ σ J (g 0 0 • x + g 1 0 • y) (g 0 1 • x + g 1 1 • y) φ)}

def LocDataV (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) : Prop :=
  IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧ SelfDual μ (fun x y => psiV F ψ v (B1 σ J v x y))

def WeilRepresentationIrreducible : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    ∀ T : ((Fin M → Fv F v ⊗[F] E) → ℂ) →ₗ[ℂ] ((Fin M → Fv F v ⊗[F] E) → ℂ),
      (∀ φ, IsSB φ → IsSB (T φ)) →
      (∀ x y φ, IsSB φ → T (rhoH (psiV F ψ v) σ J x y φ) = rhoH (psiV F ψ v) σ J x y (T φ)) →
      ∃ c : ℂ, ∀ φ, IsSB φ → T φ = c • φ

def WeilOperatorsPreserveSchwartz : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    let χ := psiV F ψ v
    ∀ φ : (Fin M → Fv F v ⊗[F] E) → ℂ, IsSB φ →
      (∀ c : Fv F v, IsSB (opU χ σ J c φ) ∧ l2 μ (opU χ σ J c φ) = l2 μ φ ∧
        ∀ x y, rhoH χ σ J x y (opU χ σ J c φ) = opU χ σ J c (rhoH χ σ J x (y + c • x) φ)) ∧
      (∀ a : Fv F v, a ≠ 0 → IsSB (opD b μ a φ) ∧ l2 μ (opD b μ a φ) = l2 μ φ ∧
        ∀ x y, rhoH χ σ J x y (opD b μ a φ) = opD b μ a (rhoH χ σ J (a • x) (a⁻¹ • y) φ)) ∧
      (IsSB (opF χ σ J μ φ) ∧ l2 μ (opF χ σ J μ φ) = l2 μ φ ∧
        ∀ x y, rhoH χ σ J x y (opF χ σ J μ φ) = opF χ σ J μ (rhoH χ σ J (-y) x φ)) ∧
      ∀ h : HA (Fv F v) σ J, let hv := fun u => (HA.mat (Fv F v) σ J h : Matrix (Fin M) (Fin M) _).mulVec u
        (∀ c, opU χ σ J c (φ ∘ hv) = opU χ σ J c φ ∘ hv) ∧ (∀ a, opD b μ a (φ ∘ hv) = opD b μ a φ ∘ hv) ∧
        opF χ σ J μ (φ ∘ hv) = opF χ σ J μ φ ∘ hv

def MetaplecticOperatorClasses : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    let χ := psiV F ψ v
    (∀ g : Matrix (Fin 2) (Fin 2) (Fv F v), g.det = 1 → (OmV χ σ J μ g).Nonempty) ∧
    (∀ g g' T T', T ∈ OmV χ σ J μ g → T' ∈ OmV χ σ J μ g' → T.comp T' ∈ OmV χ σ J μ (g * g')) ∧
    (∀ g T T', T ∈ OmV χ σ J μ g → T' ∈ OmV χ σ J μ g → g.det = 1 →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ φ, IsSB φ → T' φ = c • T φ) ∧
    (∀ c : Fv F v, ∃ T ∈ OmV χ σ J μ !![1, c; 0, 1], ∀ φ, IsSB φ → T φ = opU χ σ J c φ) ∧
    (∀ a : Fv F v, a ≠ 0 → ∃ T ∈ OmV χ σ J μ !![a, 0; 0, a⁻¹], ∀ φ, IsSB φ → T φ = opD b μ a φ) ∧
    ∃ T ∈ OmV χ σ J μ !![0, 1; -1, 0], ∀ φ, IsSB φ → T φ = opF χ σ J μ φ

def WeilIndexFourierFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    let χ := psiV F ψ v
    let r := fun β : Fv F v => (modW b μ β).toReal ^ (-(1 / 2 : ℝ))
    ∃ γ : Fv F v → ℂ, (∀ β, β ≠ 0 → ‖γ β‖ = 1) ∧
      (∀ β : Fv F v, β ≠ 0 → ∀ φ, IsSB φ →
        Fstar χ σ J μ (opF χ σ J μ φ) β = γ β * (r β : ℂ) * Fstar χ σ J μ φ (-1 / β)) ∧
      (∀ φ, IsSB φ → ∃ C : ℝ, ∀ β : Fv F v, β ≠ 0 → ‖Fstar χ σ J μ φ β‖ ≤ C * min 1 (r β)) ∧
      (IsGoodV b σ J v χ →
        (∀ β ∈ v.adicCompletionIntegers F, Fstar χ σ J μ ((latW b v).indicator 1) β = 1) ∧
        (∀ β ∉ v.adicCompletionIntegers F, ‖Fstar χ σ J μ ((latW b v).indicator 1) β‖ = r β) ∧
        ∀ β : Fv F v, Valued.v β = 1 → γ β = 1)

def MaximalCompactFiniteness : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    let χ := psiV F ψ v
    let K := {k : Matrix (Fin 2) (Fin 2) (Fv F v) | k.det = 1 ∧ ∀ i j, k i j ∈ v.adicCompletionIntegers F}
    (∀ φ, IsSB φ → ∃ (N : ℕ) (φs : Fin N → (Fin M → Fv F v ⊗[F] E) → ℂ), (∀ j, IsSB (φs j)) ∧
      ∀ k ∈ K, ∀ T ∈ OmV χ σ J μ k, ∃ j, ∃ c : ℂ, ‖c‖ = 1 ∧ T φ = c • φs j) ∧
    (IsGoodV b σ J v χ → ∀ k ∈ K, ∀ T ∈ OmV χ σ J μ k, ∃ c : ℂ, ‖c‖ = 1 ∧
      T ((latW b v).indicator 1) = c • (latW b v).indicator 1)

end Fin

def RealGaussianWeilIndex : Prop :=
  ∀ (M : ℕ) (η : Fin (2 * M) → ℝ) (ε : ℝ), (∀ l, η l = 1 ∨ η l = -1) → (ε = 1 ∨ ε = -1) →
    let q := fun u : Fin (2 * M) → ℝ => ∑ l, η l * u l ^ 2
    let qp := fun u : Fin (2 * M) → ℝ => ∑ l, u l ^ 2
    let B := fun u u' : Fin (2 * M) → ℝ => 2 * ∑ l, η l * u l * u' l
    let φ := fun (τ : ℂ) (u : Fin (2 * M) → ℝ) =>
      Complex.exp (2 * Real.pi * Complex.I * ε * τ.re * q u - 2 * Real.pi * τ.im * qp u)
    ∀ τ : ℂ, 0 < τ.im → ∃ c : ℂ, c ≠ 0 ∧ ∀ u' : Fin (2 * M) → ℝ,
      (2 : ℂ) ^ M * ∫ u, φ τ u * Complex.exp (2 * Real.pi * Complex.I * ε * B u u') = c * φ (-1 / τ) u'

end PI.GramFibrationFormulas
end
end

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def rationalSL2 (F : Type) [Field F] [NumberField F] : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (AF F)) :=
  (Matrix.SpecialLinearGroup.map (algebraMap F (AF F))).range

def SL2AdelicReductionTheory : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    (∃ (ω : Set (AF F)) (C : Set (Matrix.SpecialLinearGroup (Fin 2) (AF F))) (t₀ : ℝ),
      IsCompact ω ∧ IsCompact C ∧ 0 < t₀ ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) (AF F), ∃ γ ∈ rationalSL2 F, ∃ y ∈ ω, ∃ T : ℝ, t₀ ≤ T ∧
        ∃ a a' : Ainf F, (∀ w, a w * a' w = 1 ∧ ‖a w‖ = T) ∧ ∃ c ∈ C,
          ((γ * g : Matrix.SpecialLinearGroup (Fin 2) (AF F)) : Matrix (Fin 2) (Fin 2) (AF F)) =
            !![1, y; 0, 1] * !![pairA F a 1, 0; 0, pairA F a' 1] * (c : Matrix (Fin 2) (Fin 2) (AF F))) ∧
    letI : MeasurableSpace (Matrix.SpecialLinearGroup (Fin 2) (AF F)) := borel _
    ∃ μ : Measure (Matrix.SpecialLinearGroup (Fin 2) (AF F)), μ.IsHaarMeasure ∧
      ∃ 𝓕, IsFundamentalDomain (rationalSL2 F) 𝓕 μ ∧ μ 𝓕 < ⊤

end PI.GramFibrationFormulas
end
end

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def FinVolAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVolH σ J

def SiegelWeilFibrationFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1a1 F E σ M J

def TgtSW1a2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1a2 F E σ M J

def TgtSW1b1 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1b1 F E σ M J

def TgtSW1b2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1b2 F E σ M J

def TgtSW1c1 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1c1 F E σ M J

def SiegelWeilVolumeFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1c3 F E σ M J

def IsDxDq0 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) : Prop :=
  ν {X | ¬ (qR (AF F) σ J (X 0) = 0 ∧ FreeT (F := F) (E := E) (Ainf F) (projInf X) ∧
    (∀ v, FreeT (F := F) (E := E) (Fv F v) (projV v (projFin X))) ∧
    ∀ᶠ v in Filter.cofinite, projV v (projFin X) 0 ∈ X0int b σ J v)} = 0 ∧
  ∀ (μi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (νi : Measure (Ainf F))
    (μv : ∀ v, Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v, Measure (Fv F v)),
    SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) → SelfDual νi (fun s t => psiInf F ψ (s * t)) →
    (∀ v, SelfDual (μv v) (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y))) →
    (∀ v, SelfDual (νv v) (fun s t => psiV F ψ v (s * t))) →
  ∀ (fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E))
    (fv : ∀ v, Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
    IsQFibInf σ J μi νi fi → (∀ v, IsQFib σ J v (μv v) (νv v) (fv v)) →
  ∀ Φ Φi Φv, IsPureL b Φ Φi Φv →
    ∫⁻ X, Φ X ∂ν = (∫⁻ X, Φi X ∂(fi 0)) * ∏' v, ∫⁻ X, Φv v X ∂(fv v 0)

def NullVectorSumFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    3 ≤ M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∀ ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E), IsDxDq0 b σ J ψ ν →
    ∀ (μ : Measure (HA (AF F) σ J)) 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
    ∀ Ψ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Ψ →
      meanL μ 𝓕 (fun h => ∑' x : {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧ hE σ J (x 0) (x 0) = 0},
        Ψ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))) = ∫⁻ y, Ψ y ∂ν

def SiegelWeilFiniteVolumeCase : Prop := FinVolAll → RationalPointsLattice → IsotropicLatticeCount → SiegelWeilFibrationFormula ∧ TgtSW1a2

def SiegelWeilDensityCase : Prop :=
  FinVolAll → RationalPointsLattice → SelfDualMeasuresExist → FiniteFibreMeasureFormula → ArchimedeanFibreFamily → GlobalDensityProductFormula → HermitianDilationFormula → NullVectorSumFormula → AnisotropicOrbitSurjective → UnitaryStabilizerQuotient →
    TgtSW1b1 ∧ TgtSW1b2 ∧ SiegelWeilVolumeFormula

def SiegelWeilPureFormCase : Prop :=
  FinVolAll → RationalPointsLattice → SelfDualMeasuresExist → GramMapFibreFamily → ArchimedeanGramFibreFamily → SiegelWeilPureFormula → SchwartzBruhatConvergence → TgtSW1c1

def SiegelWeilGlobalInduction : Prop :=
  FinVolAll → RationalPointsLattice → SelfDualMeasuresExist → GramMapFibreFamily → GramFibreFamilyUnique → HaarScalingGramMap → ArchimedeanGramFibreFamily → ArchimedeanHaarScaling → WittTransitivityFreeFrames → GoodPlaceOrthonormalLattice →
    AnisotropicOrbitSurjective → UnitaryStabilizerQuotient → OrbitUnfoldingFormula → FiniteFibreMeasureFormula → ArchimedeanFibreFamily → GlobalDensityProductFormula → HermitianDilationFormula → HermitianDiagonalization → LocalInductionFinitePlace → SiegelWeilPureFormula

end PI.GramFibrationFormulas
end
end
