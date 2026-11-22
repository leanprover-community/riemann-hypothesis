module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LminorMapConj

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GradedNorm

open Matrix ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieMet
open scoped ComplexOrder

variable {m : ℕ}

variable {s : ℝ} {M₀ M : Matrix (Fin m) (Fin m) ℂ}

end GlobalTheory.GradedNorm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

namespace EigFrame

variable {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {φ' : c.F →+* R'} {x' : Sp R' ⟶ Z.X}

def IsMap (f : EigFrame Z φ x) (ψ : R →+* R') (f' : EigFrame Z φ' x') : Prop :=
  ∀ τ i, f'.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ i

theorem exists_isMap (f : EigFrame Z φ x) (ψ : R →+* R') (hφ : φ' = ψ.comp φ) (hx : x' = spMap ψ ≫ x) :
    ∃ f' : EigFrame Z φ' x', (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) ψ f' := by
  subst hφ hx
  exact exists_baseChange E H Dw l Xo c O β Z R R' φ x f ψ

variable (f g k : EigFrame Z φ x) (τ : E →+* ℂ)

def co : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R :=
  of fun a i => (f.basis τ _ (g.tan τ i) (g.eig τ i)).exists.choose a

theorem co_spec (i : Fin (Dw.mult τ)) : IsCombAtG Z.t x (f.v τ) (fun a => f.co g τ a i) (g.v τ i) :=
  (f.basis τ _ (g.tan τ i) (g.eig τ i)).exists.choose_spec

theorem vec_eq (i : Fin (Dw.mult τ)) : g.vec τ i = ∑ a, f.co g τ a i • f.vec τ a :=
  (isComb_iff (f.vec τ) _ (g.vec τ i)).1 (f.co_spec g τ i)

variable {f g τ} in
theorem co_eq {T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R}
    (h : ∀ i, IsCombAtG Z.t x (f.v τ) (fun a => T a i) (g.v τ i)) : f.co g τ = T :=
  Matrix.ext fun a i => congrFun ((f.basis τ _ (g.tan τ i) (g.eig τ i)).unique (f.co_spec g τ i) (h i)) a

theorem co_mul : f.co g τ * g.co k τ = f.co k τ := by
  refine (co_eq (T := f.co g τ * g.co k τ) fun i => (isComb_iff (f.vec τ) _ (k.vec τ i)).2 ?_).symm
  simp only [g.vec_eq k τ i, f.vec_eq g τ, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul, mul_comm]
  exact Finset.sum_comm

theorem co_self : f.co f τ = 1 :=
  co_eq (T := 1) fun i => (isComb_iff (f.vec τ) _ (f.vec τ i)).2 (by simp [Matrix.one_apply])

theorem isUnit_det_co : IsUnit (f.co g τ).det := isUnit_det_of_right_inverse ((f.co_mul g f τ).trans (f.co_self τ))

variable {f g}

theorem IsMap.co {ψ : R →+* R'} {f' g' : EigFrame Z φ' x'} (hf : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) ψ f') (hg : (_root_.GlobalTheory.ShFam.EigFrame.IsMap g) ψ g')
    (hx : x' = spMap ψ ≫ x) : f'.co g' τ = (f.co g τ).map ψ :=
  co_eq fun i => by
    rw [funext (hf τ), hg τ i]
    exact GlobalTheory.GradedPieces.comb_map ψ hx.symm (f.co_spec g τ i)

theorem Tri.co {ψ : R →+* R'} {f' g' : EigFrame Z φ' x'} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ} (h : f.Tri ψ g' t)
    (hf : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) ψ f') : (∀ a i, i < a → f'.co g' τ a i = 0) ∧ ∀ i, f'.co g' τ i i = t τ i := by
  choose T h1 h2 h3 using h.2.2 τ
  rw [co_eq (T := of fun a i => T i a) fun i => by rw [funext (hf τ)]; exact h3 i]
  exact ⟨fun a i => h2 i a, h1⟩

theorem IsMap.tri {ψ : R →+* R'} {f' : EigFrame Z φ' x'} (hf : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) ψ f') (hφ : φ' = ψ.comp φ)
    (hx : x' = spMap ψ ≫ x) : f.Tri ψ f' 1 :=
  ⟨hx, hφ, fun τ i => ⟨Pi.single i 1, by simp, fun _ hk => Pi.single_eq_of_ne hk.ne' _, by
    rw [← funext (hf τ)]; exact isCombAtG_single Z.t x' (f'.tan τ) i⟩⟩

end EigFrame

variable (Z) in
structure EigMet (σ : c.F →+* ℂ) : Type where

  gram : ∀ y : CxPts (genStr Z) σ, EigFrame Z σ (y.1 ≫ genι Z) → ∀ τ : E →+* ℂ,
    Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ
  pos : ∀ y f τ, (gram y f τ).PosDef
  change : ∀ y f g τ, gram y g τ = (f.co g τ)ᴴ * gram y f τ * f.co g τ

namespace EigMet

variable {σ : c.F →+* ℂ}

def ofForm (h : ∀ y : CxPts (genStr Z) σ, TanM (y.1 ≫ genι Z) Z.t.G →ₗ[ℂ] TanM (y.1 ≫ genι Z) Z.t.G →ₗ⋆[ℂ] ℂ)
    (hh : ∀ y, IsBlockMetric (h y)) : EigMet Z σ where
  gram y f τ := gramOf (h y) (f.vec τ)
  pos y f τ := (hh y).gram_posDef (f.linearIndependent_vec τ)
  change y f g τ := by
    ext a b
    rw [gramOf, of_apply, f.vec_eq g τ a, f.vec_eq g τ b, form_sum, Matrix.mul_assoc]
    rfl

instance : Nonempty (EigMet Z σ) := ⟨ofForm _ fun y => (exists_isBlockMetric Z.t (y.1 ≫ genι Z)).choose_spec⟩

variable {s : CxPts (genStr Z) σ → ℝ} {hs : ∀ y, s y ∈ Set.Icc (0 : ℝ) 1} {G₀ G : EigMet Z σ} {y : CxPts (genStr Z) σ}
  (f : EigFrame Z σ (y.1 ≫ genι Z)) {τ : E →+* ℂ}

variable (G) in
def SmoothOn {d : ℕ} (R : AnRead (genStr Z) σ d) (S : Set (CxPts (genStr Z) σ)) : Prop :=
  ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (τ : E →+* ℂ)
    (a b : Fin (Dw.mult τ)), LogKS.chart V ≫ genStr Z = spMap φ → ∃ g : CxPts (genStr Z) σ → ℂ,
      R.SmoothOn (S ∩ ptsIn _ σ V.1) (fun y => (g y).re) ∧ R.SmoothOn (S ∩ ptsIn _ σ V.1) (fun y => (g y).im) ∧
      ∀ y ∈ S, ∀ (hy : y ∈ ptsIn _ σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)), F.IsMap (evHom hy) f → G.gram y f τ a b = g y

end EigMet

namespace FlagCpt

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {σ : F →+* ℂ}

variable (G : EigMet Z (embOf e σ)) (n n' : Letter Dw → ℤ)

variable {Y} {p : Y.Y.pts σ} {t t₁ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ} {g g₁ : Y.FrameAt p}
  {t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℂˣ}

end FlagCpt

end GlobalTheory.ShFam
