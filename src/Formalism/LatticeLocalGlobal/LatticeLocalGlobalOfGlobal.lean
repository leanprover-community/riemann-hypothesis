import Mathlib

section
noncomputable section

namespace Formalism.LatticeLocalGlobalTheory

open IsDedekindDomain

def UniqueForm : Prop :=
  ∀ (k K E ι : Type) [Field k] [Field K] [Algebra k K] [AddCommGroup E] [Module K E]
    [Module k E] [IsScalarTower k K E] [FiniteDimensional K E]
    (ψ : ι → Module.Dual K E), (∀ v : E, (∀ i, ψ i v = 0) → v = 0) →
    ∀ W : Submodule k E, Module.finrank k W = Module.finrank K E →
      (∀ v ∈ W, ∀ i, ψ i v ∈ (algebraMap k K).range) →
      (W : Set E) = {v : E | ∀ i, ψ i v ∈ (algebraMap k K).range}

def UniqueFormTwo : Prop :=
  ∀ (k K E ι : Type) [Field k] [Field K] [Algebra k K] [AddCommGroup E] [Module K E]
    [Module k E] [IsScalarTower k K E] [FiniteDimensional K E]
    (ψ : ι → Module.Dual K E), (∀ v : E, (∀ i, ψ i v = 0) → v = 0) →
    ∀ W₁ W₂ : Submodule k E,
      Module.finrank k W₁ = Module.finrank K E → Module.finrank k W₂ = Module.finrank K E →
      (∀ v ∈ W₁, ∀ i, ψ i v ∈ (algebraMap k K).range) →
      (∀ v ∈ W₂, ∀ i, ψ i v ∈ (algebraMap k K).range) → W₁ = W₂

def OneRationalStructure : Prop :=
  ∀ (k K E ι T : Type) [Field k] [Field K] [Algebra k K] [AddCommGroup E] [Module K E]
    [Module k E] [IsScalarTower k K E] [FiniteDimensional K E]
    (Z : T → Type) [∀ μ, AddCommGroup (Z μ)] [∀ μ, Module K (Z μ)] [∀ μ, Module k (Z μ)]
    [∀ μ, IsScalarTower k K (Z μ)]
    (ψ : ι → Module.Dual K E), (∀ v : E, (∀ i, ψ i v = 0) → v = 0) →
    ∀ (io : ∀ μ, Z μ →ₗ[K] E) (FinalFormK : ∀ μ, Submodule k (Z μ)) (c : T → k)
      (vv : ∀ μ, ι → Z μ → K),
      (∀ μ, Function.Bijective (io μ)) →
      (∀ μ, Module.finrank k (FinalFormK μ) = Module.finrank K (Z μ)) →
      (∀ μ, c μ ≠ 0) →
      (∀ μ, ∀ F ∈ FinalFormK μ, ∀ i, vv μ i F ∈ (algebraMap k K).range) →
      (∀ μ, ∀ F ∈ FinalFormK μ, ∀ i, ψ i (io μ F) = (algebraMap k K (c μ))⁻¹ * vv μ i F) →
      ∀ μ μ', (FinalFormK μ).map ((io μ).restrictScalars k) = (FinalFormK μ').map ((io μ').restrictScalars k)

def IntegralOfLocalUnits : Prop :=
  ∀ (R L : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (x : L) (ζ y : HeightOneSpectrum R → L),
    (∀ w : HeightOneSpectrum R, w.valuation L (ζ w) = 1) → (∀ w : HeightOneSpectrum R, w.valuation L (y w) ≤ 1) →
    (∀ w : HeightOneSpectrum R, ζ w * x = y w) → x ∈ (algebraMap R L).range

def OneMapIntegral : Prop :=
  ∀ (R L V EE : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L]
    [AddCommGroup V] [Module L V] [Module R V] [IsScalarTower R L V]
    [AddCommGroup EE] [Module L EE] [Module R EE] [IsScalarTower R L EE]
    (N : Submodule R V) (RR : Submodule R EE) (B : V →ₗ[L] EE →ₗ[L] L)
    (ζ : HeightOneSpectrum R → L) (P : HeightOneSpectrum R → V → EE → L),
    (∀ w : HeightOneSpectrum R, w.valuation L (ζ w) = 1) →
    (∀ w : HeightOneSpectrum R, ∀ φ ∈ N, ∀ F ∈ RR, w.valuation L (P w φ F) ≤ 1) →
    (∀ (w : HeightOneSpectrum R) φ F, ζ w * B φ F = P w φ F) →
    ∃ β : N →ₗ[R] Module.Dual R RR,
      ∀ (φ : N) (F : RR), algebraMap R L (β φ F) = B (φ : V) (F : EE)

def locAt {R EE : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup EE] [Module R EE]
    (w : HeightOneSpectrum R) (M : Submodule R EE) : Set EE :=
  {x : EE | ∃ s : R, s ∉ w.asIdeal ∧ s • x ∈ M}

def LatticeLocalGlobal : Prop :=
  ∀ (R L EE : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L] [AddCommGroup EE] [Module L EE] [Module R EE] [IsScalarTower R L EE]
    (Λ₀ : Submodule R EE) (Λ : HeightOneSpectrum R → Submodule R EE)
    (S : Finset (HeightOneSpectrum R)),
    Λ₀.FG → Submodule.span L (Λ₀ : Set EE) = ⊤ →
    (∀ (w : HeightOneSpectrum R) (s : R), s ∉ w.asIdeal → ∀ x : EE, s • x ∈ Λ w → x ∈ Λ w) →
    (∀ w : HeightOneSpectrum R, w ∉ S → (Λ w : Set EE) = locAt w Λ₀) →
    (∀ w ∈ S, ∃ a : R, a ≠ 0 ∧ (∀ x ∈ locAt w Λ₀, a • x ∈ Λ w) ∧
      (∀ x ∈ Λ w, a • x ∈ locAt w Λ₀)) →
    (⨅ w, Λ w).FG ∧ Submodule.span L ((⨅ w, Λ w : Submodule R EE) : Set EE) = ⊤ ∧
      ∀ w, locAt w (⨅ w', Λ w') = (Λ w : Set EE)

def GaussSumUnit : Prop :=
  ∀ (R L : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (𝔽 : Type) [Field 𝔽] [Fintype 𝔽] (χ : MulChar 𝔽 L) (ψ : AddChar 𝔽 L),
    χ ≠ 1 → ψ.IsPrimitive →
    ∀ w : HeightOneSpectrum R, (Fintype.card 𝔽 : R) ∉ w.asIdeal →
      w.valuation L (gaussSum χ ψ) = 1

def UnitProduct : Prop :=
  ∀ (R L : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum R) (roots gs others : List L) (qs : List (R × ℤ)),
    (∀ z ∈ roots, ∃ n : ℕ, 0 < n ∧ z ^ n = 1) →
    (∀ g ∈ gs, ∃ (𝔽 : Type) (_ : Field 𝔽) (_ : Fintype 𝔽) (χ : MulChar 𝔽 L)
      (ψ : AddChar 𝔽 L), χ ≠ 1 ∧ ψ.IsPrimitive ∧ (Fintype.card 𝔽 : R) ∉ w.asIdeal ∧
        g = gaussSum χ ψ) →
    (∀ p ∈ qs, p.1 ∉ w.asIdeal) →
    (∀ c ∈ others, w.valuation L c = 1) →
    w.valuation L (roots.prod * gs.prod * (qs.map fun p => algebraMap R L p.1 ^ p.2).prod *
      others.prod) = 1

def gram {K M n : Type} [CommRing K] [StarRing K] [AddCommGroup M] [Module K M]
    (B : M →ₗ⋆[K] M →ₗ[K] K) (v : n → M) : Matrix n n K :=
  Matrix.of fun i j => B (v i) (v j)

def GramChange : Prop :=
  ∀ (K M n : Type) [CommRing K] [StarRing K] [AddCommGroup M] [Module K M] [Fintype n]
    [DecidableEq n] (B : M →ₗ⋆[K] M →ₗ[K] K) (v : n → M) (g : Matrix n n K),
    gram B (fun j => ∑ i, g i j • v i) = g.conjTranspose * gram B v * g ∧
    (gram B (fun j => ∑ i, g i j • v i)).det = star g.det * g.det * (gram B v).det

def DualGram : Prop :=
  ∀ (K M n : Type) [Field K] [StarRing K] [AddCommGroup M] [Module K M] [Fintype n]
    [DecidableEq n] (B : M →ₗ⋆[K] M →ₗ[K] K), (∀ x y, star (B x y) = B y x) →
    ∀ (v : Module.Basis n K M) (w : n → M),
      (∀ i j, B (w i) (v j) = if i = j then 1 else 0) →
      gram B w = (gram B v)⁻¹ ∧ (gram B w).det * (gram B v).det = 1

def PrincipalDatumIdentity : Prop :=
  ∀ (Γ J : Type) [CommGroup Γ] [Fintype J] (ww wwb ll : J → Γ) (e : J → ℤ)
    (c cb Nc sd ddEK A0 A0b ddE xi0 : Γ),
    (∀ j, ll j = ww j * wwb j) →
    ddEK = ∏ j, ll j ^ e j → A0 = ∏ j, ww j ^ (-e j) → A0b = ∏ j, wwb j ^ (-e j) →
    c * cb = Nc → ddE = ddEK * sd → xi0 = Nc⁻¹ * sd⁻¹ →
    xi0 * (c * A0) * (cb * A0b) * ddE = 1

end Formalism.LatticeLocalGlobalTheory
end
end

section
noncomputable section

namespace Formalism.LatticeLocalGlobalTheory

open IsDedekindDomain

def OneMapIntegralBig : Prop :=
  ∀ (R L K V EE : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L] [Field K] [Algebra L K] [Algebra R K] [IsScalarTower R L K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [AddCommGroup EE] [Module K EE] [Module R EE] [IsScalarTower R K EE]
    (N : Submodule R V) (RR : Submodule R EE) (B : V →ₗ[K] EE →ₗ[K] K)
    (ζ : HeightOneSpectrum R → L),
    Nonempty (HeightOneSpectrum R) →
    (∀ w : HeightOneSpectrum R, w.valuation L (ζ w) = 1) →
    (∀ w : HeightOneSpectrum R, ∀ φ ∈ N, ∀ F ∈ RR, ∃ p : L, w.valuation L p ≤ 1 ∧
      algebraMap L K (ζ w) * B φ F = algebraMap L K p) →
    ∃ β : N →ₗ[R] Module.Dual R RR,
      ∀ (φ : N) (F : RR), algebraMap R K (β φ F) = B (φ : V) (F : EE)

def SUnitIsUnit : Prop :=
  ∀ (R L : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (s : R) (z : L), z ≠ 0 →
    (∃ n : ℕ, IsIntegral R (algebraMap R L s ^ n * z)) →
    (∃ n : ℕ, IsIntegral R (algebraMap R L s ^ n * z⁻¹)) →
    ∀ w : HeightOneSpectrum R, s ∉ w.asIdeal → w.valuation L z = 1

def LatticeLocalGlobalOfGlobal : Prop :=
  ∀ (R L EE : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L] [AddCommGroup EE] [Module L EE] [Module R EE] [IsScalarTower R L EE]
    (Λ₀ : Submodule R EE) (Λ' : HeightOneSpectrum R → Submodule R EE)
    (S : Finset (HeightOneSpectrum R)),
    Λ₀.FG → Submodule.span L (Λ₀ : Set EE) = ⊤ →
    (∀ w, (Λ' w).FG) → (∀ w, Submodule.span L (Λ' w : Set EE) = ⊤) →
    (∀ w, w ∉ S → Λ' w = Λ₀) →
    ∃ RR : Submodule R EE, (RR : Set EE) = {x : EE | ∀ w, x ∈ locAt w (Λ' w)} ∧ RR.FG ∧
      Submodule.span L (RR : Set EE) = ⊤ ∧ ∀ w, locAt w RR = locAt w (Λ' w)

def gramσ {K M n : Type} [CommRing K] [AddCommGroup M] [Module K M] (σ : K →+* K)
    (B : M →ₛₗ[σ] M →ₗ[K] K) (v : n → M) : Matrix n n K :=
  Matrix.of fun i j => B (v i) (v j)

def GramChangeσ : Prop :=
  ∀ (K M n : Type) [CommRing K] [AddCommGroup M] [Module K M] [Fintype n] [DecidableEq n]
    (σ : K →+* K) (B : M →ₛₗ[σ] M →ₗ[K] K) (v : n → M) (g : Matrix n n K),
    gramσ σ B (fun j => ∑ i, g i j • v i) = (g.map σ).transpose * gramσ σ B v * g ∧
    (gramσ σ B (fun j => ∑ i, g i j • v i)).det = σ g.det * g.det * (gramσ σ B v).det

def DualGramσ : Prop :=
  ∀ (K M n : Type) [Field K] [AddCommGroup M] [Module K M] [Fintype n] [DecidableEq n]
    (σ : K →+* K) (B : M →ₛₗ[σ] M →ₗ[K] K), (∀ x y, σ (B x y) = B y x) →
    ∀ (v : Module.Basis n K M) (w : n → M),
      (∀ i j, B (w i) (v j) = if i = j then 1 else 0) →
      gramσ σ B w = (gramσ σ B v)⁻¹ ∧ (gramσ σ B w).det * (gramσ σ B v).det = 1

def FormIsForm : Prop :=
  ∀ (k K E ι : Type) [Field k] [Field K] [Algebra k K] [AddCommGroup E] [Module K E]
    [Module k E] [IsScalarTower k K E] [FiniteDimensional K E]
    (ψ : ι → Module.Dual K E), (∀ v : E, (∀ i, ψ i v = 0) → v = 0) →
    ∀ W : Submodule k E, Module.finrank k W = Module.finrank K E →
      (∀ v ∈ W, ∀ i, ψ i v ∈ (algebraMap k K).range) →
      ∀ (m : Type) (b : Module.Basis m k W),
        LinearIndependent K (fun j => (b j : E)) ∧
          Submodule.span K (Set.range fun j => (b j : E)) = ⊤

def IndexWellDefined : Prop :=
  ∀ (R A n : Type) [CommRing R] [AddCommGroup A] [Module R A] [Fintype n] [DecidableEq n]
    (b b' : Module.Basis n R A), IsUnit (b.toMatrix b').det

def DescendIntegral : Prop :=
  ∀ (R L X : Type) [CommRing R] [Field L] [Algebra R L] [AddCommGroup X] [Module L X]
    [Module R X] [IsScalarTower R L X]
    (Mt : Submodule R X) (U : Submodule L X) (f : X →ₗ[L] L),
    (∀ u ∈ U, f u = 0) → (∀ m ∈ Mt, f m ∈ (algebraMap R L).range) →
    ∃ g : (X ⧸ U) →ₗ[L] L, (∀ x, g (U.mkQ x) = f x) ∧
      ∀ y ∈ Mt.map ((U.mkQ).restrictScalars R), g y ∈ (algebraMap R L).range

def DetIntegral : Prop :=
  ∀ (R L n : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L] [Fintype n] [DecidableEq n]
    (w : HeightOneSpectrum R) (H : Matrix n n L) (c : L),
    (∀ i j, w.valuation L (c * H i j) ≤ 1) →
    w.valuation L (c ^ Fintype.card n * H.det) ≤ 1

def HeightFromPeriod : Prop :=
  ∀ (V EE Q : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup EE]
    [NormedSpace ℂ EE] [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (B : V →ₗ[ℂ] EE →ₗ[ℂ] ℂ) (P : V → Q → ℂ) (io : Q →ₗ[ℂ] EE) (c p : ℝ),
    Function.Surjective io → 0 < c → (∀ F, c * ‖F‖ ^ 2 ≤ ‖io F‖ ^ 2) →
    (∀ φ F, ‖B φ (io F)‖ = ‖P φ F‖) → (∀ φ F, ‖P φ F‖ ≤ p * ‖φ‖ * ‖F‖) →
    ∀ φ x, ‖B φ x‖ ^ 2 ≤ p ^ 2 / c * ‖φ‖ ^ 2 * ‖x‖ ^ 2

end Formalism.LatticeLocalGlobalTheory
end
end
