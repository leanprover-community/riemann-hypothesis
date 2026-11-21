import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import CompanionTheory.AutomorphicTheory.SegmentRepresentations.JacquetShalikaBounds.lift_levelP_alt₂
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp

section
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace CompanionTheory.jumpWindows

section Ring

variable {R : Type} [CommRing R] {a : ℕ}

def Mir (m : ℕ) (γ : GL (Fin a) R) : Prop :=
  ∀ i k : Fin a, (m ≤ (i : ℕ) ∨ m < (k : ℕ)) → γ.val i k = (1 : Matrix (Fin a) (Fin a) R) i k

def GlobalTheory (m : ℕ) (γ : GL (Fin a) R) : Prop :=
  ∀ i k : Fin a, (m ≤ (i : ℕ) ∨ m ≤ (k : ℕ)) → γ.val i k = (1 : Matrix (Fin a) (Fin a) R) i k

def lastE (k : ℕ) (y : UnipotentBlockColumnIndex a k k → R) : R := ∑ t, if (t.1.1 : ℕ) + 1 = k then y t else 0

end Ring

abbrev LieI (ι : Type) (a : ℕ) : Type := Fin a → Fin a → ι → ℂ

section Arch

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

open Classical in

def orb (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) (M : LieI ι a) : X :=
  if h : IsUnit (Matrix.of M) then ρ h.unit v else 0

def oneI (ι : Type) (a : ℕ) : LieI ι a := Matrix.of.symm 1

def SmV (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) : Prop :=
  ContDiffOn ℝ ∞ (orb ρ v) {M | IsUnit (Matrix.of M)}

def RapidFam {V : Type} [NormedAddCommGroup V] (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X))
    (𝒢 : Submodule ℂ (V → X)) : Prop :=
  ∀ G ∈ 𝒢, Continuous G ∧ (∀ N : ℕ, ∃ C : ℝ, ∀ y, (1 + ‖y‖) ^ N * ‖G y‖ ≤ C) ∧
    ∃ D : LieI ι a → V → X, (∀ Z, D Z ∈ 𝒢) ∧
      ∀ y, ∃ D' : LieI ι a →L[ℝ] X, (∀ Z, D' Z = D Z y) ∧ HasFDerivAt (orb ρ (G y)) D' (oneI ι a)

end Arch

def FT {V X : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [NormedAddCommGroup X]
    [NormedSpace ℂ X] (μ : Measure V) (β : V →L[ℝ] V →L[ℝ] ℝ) (F : V → X) (y : V) : X :=
  ∫ x, Complex.exp (-(β x y : ℝ) * Complex.I) • F x ∂μ

def PolyBd {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (g : GL (Fin a) (ι → ℂ)) x, ‖ρ g x‖ ≤
    C * (1 + ‖(Matrix.of.symm g.val : LieI ι a)‖ + ‖(Matrix.of.symm g⁻¹.val : LieI ι a)‖) ^ N * ‖x‖

def ForIso (P : ∀ (ι : Type) [Fintype ι] (a : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X],
    (GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) → Prop) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)), PolyBd ρ → P ι a X ρ

def ForV (P : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V], Measure V → Prop) : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure], P V μ

def S1 : Prop := ForIso fun ι _ a X _ _ ρ => ∀ 𝒮 : Submodule ℂ X,
  (∀ v ∈ 𝒮, ∃ D : LieI ι a →L[ℝ] X, HasFDerivAt (orb ρ v) D (oneI ι a) ∧ ∀ Z, D Z ∈ 𝒮) → ∀ v ∈ 𝒮, SmV ρ v

def S2 : Prop := ForIso fun ι _ a X _ _ ρ =>
  SmV ρ 0 ∧ (∀ v w, SmV ρ v → SmV ρ w → SmV ρ (v + w)) ∧ (∀ (c : ℂ) v, SmV ρ v → SmV ρ (c • v)) ∧
  (∀ g v, SmV ρ v → SmV ρ (ρ g v)) ∧
  (∀ T : X →L[ℂ] X, (∀ g x, T (ρ g x) = ρ g (T x)) → ∀ v, SmV ρ v → SmV ρ (T v)) ∧
  ∀ v, SmV ρ v → ∃ D : LieI ι a →L[ℝ] X, HasFDerivAt (orb ρ v) D (oneI ι a) ∧ ∀ Z, SmV ρ (D Z)

def S3 : Prop := ForIso fun ι _ a X _ _ ρ => ForV fun V _ _ _ μ =>
  ∀ (u : V → GL (Fin a) (ι → ℂ)) (L : V →L[ℝ] LieI ι a), (∀ y, (u y).val = 1 + Matrix.of (L y)) →
    (∀ y, (u y)⁻¹.val = 1 - Matrix.of (L y)) → ∀ 𝒢 : Submodule ℂ (V → X), RapidFam ρ 𝒢 →
    ∀ G ∈ 𝒢, Integrable (fun y => ρ (u y) (G y)) μ ∧ SmV ρ (∫ y, ρ (u y) (G y) ∂μ)

def S4 : Prop := ForV fun V _ _ _ μ => ∀ β : V →L[ℝ] V →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) →
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (F : V → X), ContDiff ℝ ∞ F →
    HasCompactSupport F → Continuous (FT μ β F) ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ y, (1 + ‖y‖) ^ N * ‖FT μ β F y‖ ≤ C

def S5 : Prop := ForV fun V _ _ _ μ => ∀ β : V →L[ℝ] V →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) →
  ∃ c : ℂ, c ≠ 0 ∧ ∀ f : V → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ ξ,
    ∫ y, Complex.exp ((β ξ y : ℝ) * Complex.I) * FT μ β f y ∂μ = c * f ξ

def S6 : Prop := ForIso fun ι _ a X _ _ ρ => ForV fun V _ _ _ μ =>
  ∀ β : V →L[ℝ] V →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) → ∀ (O : Set V) (σ τ : V → LieI ι a), IsOpen O →
    ContDiffOn ℝ ∞ σ O → ContDiffOn ℝ ∞ τ O → (∀ x ∈ O, Matrix.of (σ x) * Matrix.of (τ x) = 1) →
    ∃ 𝒢 : Submodule ℂ (V → X), RapidFam ρ 𝒢 ∧ ∀ (η : V → ℂ) (w : X), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ O → SmV ρ w → FT μ β (fun x => η x • orb ρ w (σ x)) ∈ 𝒢

def S8 : Prop := ∀ (ι : Type) [Fintype ι] (χ : AddChar (ι → ℂ) ℂ), Continuous χ → (∀ z, ‖χ z‖ = 1) →
  ∃ l : (ι → ℂ) →L[ℝ] ℝ, ∀ z, χ z = Complex.exp ((l z : ℝ) * Complex.I)

def S7 : Prop := ForIso fun ι _ a X _ _ ρ => ∀ m : ℕ, m + 1 < a → ∀ χ : AddChar (ι → ℂ) ℂ, Continuous χ →
  (∀ z, ‖χ z‖ = 1) → (∀ z, (∀ w, χ (z * w) = 1) → z = 0) → ∀ U ∈ 𝓝 (1 : GL (Fin a) (ι → ℂ)),
  ∃ (η : GL (Fin a) (ι → ℂ) → ℂ) (r : GL (Fin a) (ι → ℂ) → GL (Fin a) (ι → ℂ)), η 1 ≠ 0 ∧ r 1 = 1 ∧
    (∀ h, GlobalTheory (m + 1) h → η h ≠ 0 → Mir m (r h)) ∧ (∀ h, ∃ t : ℝ, 0 ≤ t ∧ η h = t) ∧
    (∃ C, IsCompact C ∧ C ⊆ U ∧ (∀ c ∈ C, GlobalTheory (m + 1) c) ∧ ∀ h, GlobalTheory (m + 1) h → η h ≠ 0 → ∃ c ∈ C, h = r h * c) ∧
    ∀ v, SmV ρ v → ∃ v', SmV ρ v' ∧
      ∀ Y : Submodule ℂ X, IsClosed (Y : Set X) → (∀ g, ∀ x ∈ Y, ρ g x ∈ Y) → v ∈ Y → v' ∈ Y ∧
        ∀ Λ : X →L[ℂ] ℂ, (∀ x ∈ Y, ∀ y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → ι → ℂ,
          Λ (ρ (blkU y) x) = χ (lastE (m + 1) y) * Λ x) → ∀ h, GlobalTheory (m + 1) h → Λ (ρ h v') = η h * Λ (ρ (r h) v)

def S9 : Prop := ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (a m : ℕ), m + 1 < a → ∀ χ : AddChar F ℂ, Continuous χ → (∃ x, χ x ≠ 1) →
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (Fin a) F) X) (U : Set (GL (Fin a) F)),
    U ∈ 𝓝 (1 : GL (Fin a) F) →
    ∃ (T : Finset (GL (Fin a) F)) (c η : GL (Fin a) F → ℂ) (r : GL (Fin a) F → GL (Fin a) F), η 1 ≠ 0 ∧ r 1 = 1 ∧
      (∀ h, GlobalTheory (m + 1) h → η h ≠ 0 → Mir m (r h)) ∧ (∀ h, ∃ t : ℝ, 0 ≤ t ∧ η h = t) ∧
      (∃ C, IsCompact C ∧ C ⊆ U ∧ (∀ c ∈ C, GlobalTheory (m + 1) c) ∧ ∀ h, GlobalTheory (m + 1) h → η h ≠ 0 → ∃ c ∈ C, h = r h * c) ∧
      ∀ v, (∀ u ∈ U, ρ u v = v) →
        ∀ Y : Submodule ℂ X, (∀ g, ∀ x ∈ Y, ρ g x ∈ Y) → v ∈ Y →
          ∀ Λ : X →ₗ[ℂ] ℂ, (∀ x ∈ Y, ∀ y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F,
            Λ (ρ (blkU y) x) = χ (lastE (m + 1) y) * Λ x) →
            ∀ h, GlobalTheory (m + 1) h → Λ (ρ h (∑ t ∈ T, c t • ρ t v)) = η h * Λ (ρ (r h) v)

def MirabolicColumnBlock : Prop := ∀ (R : Type) [CommRing R] (a m : ℕ),
  (∀ γ : GL (Fin a) R, Mir m γ → ∃ (y : UnipotentBlockColumnIndex a m m → R) (h : GL (Fin a) R), GlobalTheory m h ∧ γ = blkU y * h) ∧
  (∀ γ : GL (Fin a) R, Mir 0 γ → γ = 1) ∧ Mir m (1 : GL (Fin a) R) ∧ GlobalTheory m (1 : GL (Fin a) R) ∧
  (∀ γ γ' : GL (Fin a) R, Mir m γ → Mir m γ' → Mir m (γ * γ')) ∧
  (∀ (k : ℕ) (y : UnipotentBlockColumnIndex a k k → R), k ≤ m → Mir m (blkU y)) ∧
  (∀ (k : ℕ) (γ : GL (Fin a) R), k ≤ m → Mir k γ → Mir m γ) ∧
  ∀ h : GL (Fin a) R, GlobalTheory m h → ∀ y : UnipotentBlockColumnIndex a m m → R, ∃ y' : UnipotentBlockColumnIndex a m m → R, h * blkU y = blkU y' * h ∧
    ∀ t, y' t = ∑ s, h.val t.1.1 s.1.1 * y s

end CompanionTheory.jumpWindows

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace CompanionTheory.jumpWindows

abbrev Pl (E : Type) [Field E] [NumberField E] : Type := HeightOneSpectrum (𝓞 E)

abbrev XB (E : Type) [Field E] [NumberField E] (a : ℕ) : Type := GA E a →ᵇ ℂ

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def rtFun (h : GA E a) (φ : XB E a) : XB E a := φ.compContinuous ⟨fun g => g * h, continuous_mul_right h⟩

variable (E a) in

def Rt : GA E a →* (XB E a →L[ℂ] XB E a) where
  toFun h := LinearMap.mkContinuous
    { toFun := rtFun h, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } 1
    fun φ => by rw [one_mul]; exact norm_compContinuous_le _ _
  map_one' := by ext φ g; change φ (g * 1) = φ g; rw [mul_one]
  map_mul' h k := by ext φ g; change φ (g * (h * k)) = φ (g * h * k); rw [mul_assoc]

@[simp] theorem Rt_apply (h g : GA E a) (φ : XB E a) : Rt E a h φ g = φ (g * h) := rfl

def fl (a : ℕ) (w : Pl E) : GL (Fin a) (w.adicCompletion E) →* GA E a := (finGL E a).comp (locGL E a w)

def cLoc (w : Pl E) : GA E a →* GL (Fin a) (w.adicCompletion E) :=
  GeneralLinearGroup.map ((pLoc E w).comp (pFin E))

def repW (a : ℕ) (w : Pl E) : Representation ℂ (GL (Fin a) (w.adicCompletion E)) (XB E a) :=
  (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp (Rt E a)).comp (fl a w)

@[simp] theorem repW_apply (w : Pl E) (u : GL (Fin a) (w.adicCompletion E)) (φ : XB E a) :
    repW a w u φ = Rt E a (fl a w u) φ := rfl

def SatFn (w : Pl E) (B : Multiset ℂˣ) (φ : XB E a) : Prop := φ = 0 ∨ IsSatVecGL w (repW a w) φ B

def Cond (ψ : AddChar (Ad E) ℂ) (w : Pl E) : Prop :=
  (∀ y ∈ Ov E w, ψ (sFin E (sLoc E w y)) = 1) ∧
    ∃ ϖ y : w.adicCompletion E, IsUnifV E w ϖ ∧ ϖ * y ∈ Ov E w ∧ ψ (sFin E (sLoc E w y)) ≠ 1

def Wh (ψ : AddChar (Ad E) ℂ) (φ : XB E a) : GA E a → ℂ := whit ψ (a - 1) φ

def Lev (S : Finset (Pl E)) (φ : XB E a) : Prop := ∀ w ∈ S, {u | repW a w u φ = φ} ∈ 𝓝 (1 : GL (Fin a) (w.adicCompletion E))

def InS (S : Finset (Pl E)) (g : GA E a) : Prop := ∀ w, w ∉ S → cLoc w g = 1

structure YOK (ψ : AddChar (Ad E) ℂ) (S : Finset (Pl E)) (Y : Submodule ℂ (XB E a)) : Prop where
  closed : IsClosed (Y : Set (XB E a))
  stable : ∀ g, InS S g → ∀ φ ∈ Y, Rt E a g φ ∈ Y
  good : ∀ φ ∈ Y, Good ψ (a - 1) φ

variable [IsTotallyComplex E]

def cInf : GA E a →* GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E)

variable (E a) in

def repI : GL (Fin a) (Cinf E) →* (XB E a →L[ℂ] XB E a) := (Rt E a).comp (infGL E a)

def Om (n : ℕ) (m : Pl E → ℕ) (g : GA E a) : Prop := Mir n (cInf g) ∧ ∀ w, Mir (m w) (cLoc w g)

def MirS (S : Finset (Pl E)) (g : GA E a) : Prop := Mir (a - 1) (cInf g) ∧ ∀ w ∈ S, Mir (a - 1) (cLoc w g)

def St (ψ : AddChar (Ad E) ℂ) (S : Finset (Pl E)) (Y Y' : Submodule ℂ (XB E a)) (n : ℕ) (m : Pl E → ℕ) : Prop :=
  ∃ φ ∈ Y, ∃ φ' ∈ Y', SmV (repI E a) φ ∧ SmV (repI E a) φ' ∧ Lev S φ ∧ Lev S φ' ∧ Wh ψ φ 1 ≠ 0 ∧
    ∀ g, Om n m g → Wh ψ φ g = Wh ψ φ' g

def ForE (P : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], ℕ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), P E a

def G0 : Prop := ForE fun E _ _ _ a =>
  (∀ y, cInf (infGL E a y) = y) ∧ (∀ w y, cLoc w (infGL E a y) = 1) ∧ (∀ w u, cInf (fl a w u : GA E a) = 1) ∧
  (∀ w u, cLoc w (fl a w u : GA E a) = u) ∧ (∀ w v u, v ≠ w → cLoc v (fl a w u : GA E a) = 1) ∧
  (∀ g h : GA E a, cInf g = cInf h → (∀ w, cLoc w g = cLoc w h) → g = h) ∧
  (∀ g : GA E a, cInf g = 1 → ∀ y, g * infGL E a y = infGL E a y * g) ∧
  (∀ w (g : GA E a), cLoc w g = 1 → ∀ u, g * fl a w u = fl a w u * g) ∧
  (∀ k (y : UnipotentBlockColumnIndex a k k → Cinf E), infGL E a (blkU y) = blkU fun t => sInf E (y t)) ∧
  (∀ w k (y : UnipotentBlockColumnIndex a k k → w.adicCompletion E), fl a w (blkU y) = blkU fun t => sFin E (sLoc E w (y t))) ∧
  (∀ (S : Finset (Pl E)) (g : GA E a), ∃ g₀ : GA E a, cInf g₀ = cInf g ∧ (∀ w ∈ S, cLoc w g₀ = cLoc w g) ∧ InS S g₀) ∧
  Continuous (cInf : GA E a → _) ∧ (∀ w, Continuous (cLoc w : GA E a → _)) ∧ (∀ w : Pl E, Continuous (fl a w)) ∧
  Continuous (infGL E a)

def G1 : Prop := ForE fun E _ _ _ a => ∀ π : CuspSub E a, IsNormalised π → ∀ φ ∈ π.V,
  ∃ x : XB E a, (x : GA E a → ℂ) = φ.1 ∧ SmV (repI E a) x ∧ ∀ S, Lev S x

def AlmostEverywhereSpherical : Prop := ForE fun E _ _ _ a => ∀ π : CuspSub E a, IsNormalised π → ∀ φ ∈ π.V, ∀ x : XB E a, (x : GA E a → ℂ) = φ.1 →
  ∀ᶠ w in cofinite, ∀ B, (CG.mk π).HasSat w B → SatFn w B x

def G2a : Prop := ForE fun E _ _ _ a => ∀ ψ, StdPsi ψ → ∃ Y : Submodule ℂ (XB E a), IsClosed (Y : Set (XB E a)) ∧
  (∀ g, ∀ φ ∈ Y, Rt E a g φ ∈ Y) ∧ ∀ φ : XB E a, φ ∈ Y ↔ Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g

def G2b : Prop := ForE fun E _ _ _ a => ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (H : Submodule ℂ (L2 (latticeGL E a) μ)), IsSubrep (R (latticeGL E a) μ) H →
  ∃ Y : Submodule ℂ (XB E a), IsClosed (Y : Set (XB E a)) ∧ (∀ g, ∀ φ ∈ Y, Rt E a g φ ∈ Y) ∧
    ∀ φ : XB E a, φ ∈ Y ↔ ∃ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ H

def G2c : Prop := ForE fun E _ _ _ a => ∀ (w : Pl E) (B : Multiset ℂˣ), B.card = a →
  ∃ Y : Submodule ℂ (XB E a), IsClosed (Y : Set (XB E a)) ∧ (∀ g, cLoc w g = 1 → ∀ φ ∈ Y, Rt E a g φ ∈ Y) ∧
    ∀ φ : XB E a, φ ∈ Y ↔ SatFn w B φ

def G5 : Prop := ForE fun E _ _ _ a => ∀ ψ, StdPsi ψ →
  (∀ g : GA E a, ∃ Λ : XB E a →L[ℂ] ℂ, ∀ φ : XB E a, Good ψ (a - 1) φ → Λ φ = Wh ψ φ g) ∧
  (∀ (φ : XB E a) (g h : GA E a), Wh ψ (Rt E a h φ) g = Wh ψ φ (g * h)) ∧
  (∀ (φ : XB E a) (h : GA E a), Good ψ (a - 1) φ → Good ψ (a - 1) (Rt E a h φ)) ∧
  ∀ φ : XB E a, Good ψ (a - 1) φ → Continuous (Wh ψ φ) ∧ (φ ≠ 0 → ∃ g, Wh ψ φ g ≠ 0) ∧
    ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, Wh ψ φ (blkU y * g) = ψ (lastE k y) * Wh ψ φ g

def G5b : Prop := ForE fun E _ _ _ a => ∀ S : Finset (Pl E),
  (∀ (g : GA E a) φ, SmV (repI E a) φ → SmV (repI E a) (Rt E a g φ)) ∧
  (∀ (g : GA E a) φ, Lev S φ → Lev S (Rt E a g φ)) ∧
  (∀ (c : ℂ) (φ : XB E a), Lev S φ → Lev S (c • φ)) ∧ (∀ φ φ' : XB E a, Lev S φ → Lev S φ' → Lev S (φ + φ')) ∧
  Lev S (0 : XB E a)

def G6 : Prop := ForE fun E _ _ _ a => ∀ ψ, StdPsi ψ → ∀ (S : Finset (Pl E)) (Y Y' : Submodule ℂ (XB E a)),
  YOK ψ S Y → YOK ψ S Y' → ∀ n m, n + 1 < a → St ψ S Y Y' n m → St ψ S Y Y' (n + 1) m

open Classical in

def G7 : Prop := ForE fun E _ _ _ a => ∀ ψ, StdPsi ψ → ∀ (S : Finset (Pl E)) (Y Y' : Submodule ℂ (XB E a)),
  YOK ψ S Y → YOK ψ S Y' → ∀ n m, ∀ w ∈ S, m w + 1 < a → St ψ S Y Y' n m →
    St ψ S Y Y' n (Function.update m w (m w + 1))

open Classical in

def FourierInductionSteps : Prop := ForE fun E _ _ _ a => ∀ ψ, StdPsi ψ → ∀ (S : Finset (Pl E)) (Y Y' : Submodule ℂ (XB E a)),
  YOK ψ S Y → YOK ψ S Y' → St ψ S Y Y' 0 (fun _ => 0) → St ψ S Y Y' (a - 1) fun w => if w ∈ S then a - 1 else 0

def G9 : Prop := ForE fun E _ _ _ a => ∀ ψ, StdPsi ψ → ∀ w, Cond ψ w → ∀ (B : Multiset ℂˣ) (φ : XB E a),
  Good ψ (a - 1) φ → SatFn w B φ → ∀ h, cLoc w h = 1 → Wh ψ φ h = 0 → ∀ u, Wh ψ φ (h * fl a w u) = 0

def PlacewiseToOutsideS : Prop := ForE fun E _ _ _ a => ∀ (S : Finset (Pl E)) (f : GA E a → ℂ), Continuous f →
  (∀ w, w ∉ S → ∀ h, cLoc w h = 1 → f h = 0 → ∀ u, f (h * fl a w u) = 0) →
  ∀ g g₀ : GA E a, cInf g₀ = cInf g → (∀ w ∈ S, cLoc w g₀ = cLoc w g) → InS S g₀ → f g₀ = 0 → f g = 0

def G8 : Prop := ForE fun E _ _ _ a => ∀ ψ, StdPsi ψ → ∀ (S : Finset (Pl E)), (∀ w, w ∉ S → Cond ψ w) →
  ∀ Y : Submodule ℂ (XB E a), YOK ψ S Y → ∀ φ ∈ Y, φ ≠ 0 → SmV (repI E a) φ → Lev S φ →
    (∀ w, w ∉ S → ∃ B, SatFn w B φ) → ∃ φ₁ ∈ Y, SmV (repI E a) φ₁ ∧ Lev S φ₁ ∧ Wh ψ φ₁ 1 = 1

def StandardCharacterExists : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E],
  ∃ ψ : AddChar (Ad E) ℂ, StdPsi ψ ∧ ∀ᶠ w in cofinite, Cond ψ w

def FourierUniquenessMirabolic : Prop := ForE fun E _ _ _ a => ∀ ψ, StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), (m < a ∨ m = 0) → Good ψ m f →
  ∀ Z : Set (GA E a), (∀ γ, IsMir m γ → ∀ g ∈ Z, ratGL E a γ * g ∈ Z) →
    (∀ k ≤ m, ∀ y : UnipotentBlockColumnIndex a k k → Ad E, ∀ g ∈ Z, blkU y * g ∈ Z) →
    (∀ g ∈ Z, whit ψ m f g = 0) → ∀ g ∈ Z, f g = 0

def WeakApproximationGL : Prop := ForE fun E _ _ _ a => ∀ S : Finset (Pl E),
  Dense {x : GA E a | ∃ γ g, x = ratGL E a γ * g ∧ cInf g = 1 ∧ ∀ w ∈ S, cLoc w g = 1}

def WhittakerVanishingImpliesZero : Prop := ForE fun E _ _ _ a => ∀ ψ, StdPsi ψ → ∀ (S : Finset (Pl E)), (∀ w, w ∉ S → Cond ψ w) →
  ∀ φ : XB E a, Good ψ (a - 1) φ → (∀ γ g, φ (ratGL E a γ * g) = φ g) → (∀ w, w ∉ S → ∃ B, SatFn w B φ) →
    (∀ g, MirS S g → InS S g → Wh ψ φ g = 0) → φ = 0

def SameSat (π π' : CuspSub E a) : Prop := ∀ᶠ w in cofinite, ∃ B, (CG.mk π).HasSat w B ∧ (CG.mk π').HasSat w B

def Meet : Prop := ForE fun E _ _ _ a => ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (π π' : CuspSub E a) (H H' : Submodule ℂ (L2 (latticeGL E a) μ)), IsNormalised π → IsNormalised π' →
  IsSubrep (R (latticeGL E a) μ) H → IsSubrep (R (latticeGL E a) μ) H' →
  (∀ φ ∈ π.V, ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) →
  (∀ φ ∈ π'.V, ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H') → SameSat π π' → H ⊓ H' ≠ ⊥

def CuspidalIrreducibleSubrep : Prop := ForE fun E _ _ _ a => ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (π : CuspSub E a), IsNormalised π → ∃ H, IsIrredSubrep (R (latticeGL E a) μ) H ∧ IsFinitePartOf μ π H

def SmoNorm : Prop := ForE fun E _ _ _ a => ∀ π π' : CuspSub E a, IsNormalised π → IsNormalised π' →
  SameSat π π' → π = π'

def HeckeCharacterRigidity : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (ω ω' : HChar E),
  (∀ᶠ w in cofinite, ω.val w = ω'.val w) → ω = ω'

def Smo : Prop := ForE fun E _ _ _ a => ∀ π π' : CuspSub E a, SameSat π π' → π = π'

end CompanionTheory.jumpWindows

end
end
