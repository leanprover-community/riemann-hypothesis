import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerMemDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkDcrisLSumZero

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD
  Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

def DRFree : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      Module.Free O (RR W T₂ i (b i + S)) ∧ Module.Finite O (RR W T₂ i (b i + S))

def DRQEta : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d, ∀ x ∈ NDl W T₂ i,
      Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ PhiPullΔ W T₂ i

def DRLat (hπ : W.π₀ ∈ W.AΔ) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → ↥(NDl W T₂ i)) (k : Fin m' → ℕ),
        (∃ e : ↥(RRp W T₂ hπ i (b i + S) g) ≃ₗ[O] ((j : Fin m') → Aq O (k j)),
          ∀ (x : ↥(RRp W T₂ hπ i (b i + S) g)) (j : Fin m'),
            e ⟨qR W T₂ hπ i (b i + S) x, RRp_stable W T₂ hπ i (b i + S) g x x.2⟩ j =
              Ideal.Quotient.mk _ PowerSeries.X * e x j) ∧
        (∀ (z : RR W T₂ i (b i + S)) (t : ℕ), ((PD.p : ℕ) : O) ^ t • z ∈ RRp W T₂ hπ i (b i + S) g →
          ((PD.p : ℕ) : O) ^ (2 * ⌊cD PD.p (hpar n b S + η)⌋₊) • z ∈ RRp W T₂ hπ i (b i + S) g) ∧
        finrank O (RR W T₂ i (b i + S) ⧸ satL ((PD.p : ℕ) : O) (RRp W T₂ hπ i (b i + S) g)) ≤
          finrank LL T₂.V * S





def lowSum (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (h η : ℕ) : ℤ :=
  ∑ u ∈ Finset.Icc (-(η : ℤ)) η, multV PD T.ρ τ u * ((h : ℤ) + u)

def DRRank (hπ : W.π₀ ∈ W.AΔ) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d, ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∀ (m' : ℕ) (g : Fin m' → ↥(NDl W T₂ i)) (k : Fin m' → ℕ)
        (_ : ↥(RRp W T₂ hπ i (b i + S) g) ≃ₗ[O] ((j : Fin m') → Aq O (k j))),
        lowSum (PD := PD) T₂ τ (b i + S) η ≤ ∑ j, (k j : ℤ) →
        finrank O (RR W T₂ i (b i + S) ⧸ satL ((PD.p : ℕ) : O) (RRp W T₂ hπ i (b i + S) g)) ≤
          finrank LL T₂.V * S

def WachQuotientCyclicDecomposition (hπ : W.π₀ ∈ W.AΔ) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → ↥(NDl W T₂ i)) (k : Fin m' → ℕ),
        (∃ e : ↥(RRp W T₂ hπ i (b i + S) g) ≃ₗ[O] ((j : Fin m') → Aq O (k j)),
          ∀ (x : ↥(RRp W T₂ hπ i (b i + S) g)) (j : Fin m'),
            e ⟨qR W T₂ hπ i (b i + S) x, RRp_stable W T₂ hπ i (b i + S) g x x.2⟩ j =
              Ideal.Quotient.mk _ PowerSeries.X * e x j) ∧
        (∀ (z : RR W T₂ i (b i + S)) (t : ℕ), ((PD.p : ℕ) : O) ^ t • z ∈ RRp W T₂ hπ i (b i + S) g →
          ((PD.p : ℕ) : O) ^ (2 * ⌊cD PD.p (hpar n b S + η)⌋₊) • z ∈ RRp W T₂ hπ i (b i + S) g) ∧
        ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i → lowSum (PD := PD) T₂ τ (b i + S) η ≤ ∑ j, (k j : ℤ)



end Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut
