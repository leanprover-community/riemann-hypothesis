module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open scoped ContDiff ComplexOrder

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ}

namespace CxPts

variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {y : CxPts p σ} {f f' : CxPts p σ → F}

def VInfAt (f : CxPts p σ → F) (y : CxPts p σ) : Prop :=
  ∃ (W : X.Opens) (ι : Type) (_ : Fintype ι) (g : ι → Γ(X, W)) (Φ : (ι → ℂ) → F) (O : Set (ι → ℂ)),
    y ∈ ptsIn p σ W ∧ IsOpen O ∧ (fun a => ev p σ W (g a) y) ∈ O ∧ ContDiffOn ℝ ∞ Φ O ∧
      f =ᶠ[𝓝 y] fun z => Φ fun a => ev p σ W (g a) z

theorem vInfAt_iff_cInfAt {u : CxPts p σ → ℝ} : VInfAt u y ↔ CInfAt u y := Iff.rfl

theorem VInfAt.comp (h : VInfAt f y) {Ψ : F → G} {T : Set F} (hT : IsOpen T) (hy : f y ∈ T)
    (hΨ : ContDiffOn ℝ ∞ Ψ T) : VInfAt (fun z => Ψ (f z)) y := by
  obtain ⟨W, ι, _, g, Φ, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨W, ι, inferInstance, g, Ψ ∘ Φ, O ∩ Φ ⁻¹' T, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ hT, ⟨h₃, ?_⟩,
    hΨ.comp (h₄.mono inter_subset_left) fun _ hv => hv.2, h₅.fun_comp Ψ⟩
  rw [mem_preimage, ← h₅.eq_of_nhds]
  exact hy

theorem VInfAt.comp_contDiff (h : VInfAt f y) {Ψ : F → G} (hΨ : ContDiff ℝ ∞ Ψ) :
    VInfAt (fun z => Ψ (f z)) y := h.comp isOpen_univ trivial hΨ.contDiffOn

theorem VInfAt.contDiffAt_chart (h : VInfAt f y) {D : ℕ} (c : AlgChart p σ D)
    (hy : y ∈ c.e.source) : ContDiffAt ℝ ∞ (fun v => f (c.e.symm v)) (c.e y) := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) W)
  have e := c.e.left_inv hy
  have hg : ContDiffAt ℝ ∞ (fun w a => ev p σ W (g a) (c.e.symm w)) (c.e y) :=
    contDiffAt_pi.2 fun a => (ChartGlue.contDiffOn_real ho (c.holo W (g a))).contDiffAt
      (ho.mem_nhds (ChartGlue.mem_over c.e hy h₁))
  have h₆ : ContDiffAt ℝ ∞ F (fun a => ev p σ W (g a) (c.e.symm (c.e y))) := by
    rw [e]; exact h₄.contDiffAt (h₂.mem_nhds h₃)
  refine (h₆.comp (c.e y) hg).congr_of_eventuallyEq ?_
  have := c.e.continuousAt_symm (c.e.map_source hy)
  rw [ContinuousAt, e] at this
  exact this.eventually h₅

theorem mem_ptsIn_iff_of_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {W : X.Opens} : y' ∈ ptsIn p σ' W ↔ y ∈ ptsIn p σ W := by
  have e : y'.1 (IsLocalRing.closedPoint ℂ) = y.1 (IsLocalRing.closedPoint ℂ) := by
    rw [h]
    exact congrArg y.1 (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _)
  rw [mem_ptsIn, mem_ptsIn, e]

end CxPts

namespace VB.Chart

variable {E : X.Modules} {r : ℕ} (c c' c'' : Chart E r) {V W : X.Opens} {y : CxPts p σ}

end VB.Chart

namespace HermFrame

variable {m n l : Type} [Fintype m] [Fintype n] [Fintype l]

def chg (A : Matrix n m ℂ) (H : Matrix n n ℂ) : Matrix m m ℂ := Aᵀ * H * Aᴴᵀ

end HermFrame

namespace CxPts

variable {m n l : Type} {y : CxPts p σ}

def MInfAt (A : CxPts p σ → Matrix m n ℂ) (y : CxPts p σ) : Prop :=
  ∀ a b, VInfAt (fun z => A z a b) y

variable {A A' : CxPts p σ → Matrix m n ℂ}

variable [Fintype m] [Fintype n]

end CxPts

@[ext] structure Met (p : X ⟶ Sp k) (σ : k →+* ℂ) (E : X.Modules) (r : ℕ) where

  isVB : IsVB E r

  G : Chart E r → CxPts p σ → Matrix (Fin r) (Fin r) ℂ

  posDef : ∀ c y, y ∈ ptsIn p σ c.U → (G c y).PosDef

  trans : ∀ c c' y, y ∈ ptsIn p σ c.U → G c' y = chg (c.tr p σ c' y) (G c y)

namespace Met

variable {E E' : X.Modules} {r : ℕ} (h : Met p σ E r) {V W : X.Opens} {y : CxPts p σ}

variable {h}

end Met

namespace Met

variable {E E' : X.Modules} {r : ℕ} {h : Met p σ E r} {h' : Met p σ' E r}

end Met

@[ext] structure VMetric (p : X ⟶ Sp k) (E : X.Modules) (r : ℕ) where

  isVB : IsVB E r

  met : ∀ σ : k →+* ℂ, Met p σ E r

  conj : ∀ σ σ', (met σ).IsConj (met σ')

namespace VMetric

variable {E E' E₁ E₂ : X.Modules} {r r₁ r₂ : ℕ} (h : VMetric p E r)

variable {h}

end VMetric

namespace HermVB

variable {r : ℕ} (E : HermVB p r)

end HermVB

end GlobalTheory
