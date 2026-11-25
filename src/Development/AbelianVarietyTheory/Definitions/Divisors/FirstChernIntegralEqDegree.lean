module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section

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

end CxPts

namespace VB.Chart

variable {E : X.Modules} {r : ℕ} (c c' c'' : Chart E r) {V W : X.Opens} {y : CxPts p σ}

variable (p σ) in
def crd (s : Γ(E, V)) (y : CxPts p σ) : Fin r → ℂ := fun a =>
  ev p σ (V ⊓ c.U) ((c.isFrame.basis inf_le_right).repr (resM E inf_le_left s) a) y

variable (p σ) in
def tr (y : CxPts p σ) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => c.crd p σ (c'.e b) y a

def pull (hE : IsVB E r) (π : Y ⟶ X) : Chart ((Scheme.Modules.pullback π).obj E) r :=
  have := hE.isQuasicoherent
  ⟨π ⁻¹ᵁ c.U, _, c.isFrame.pullback π⟩

def dual : Chart (VB.dual E) r := by
  let d (i : Fin r) : Γ(VB.dual E, c.U) :=
    homMk (G := SheafOfModules.unit X.ringCatSheaf) (fun _ h => (c.isFrame.basis h).coord i)
      (fun _ _ h h' s => c.isFrame.repr_resM h h' s i)
  refine ⟨c.U, d, fun V h => ?_⟩
  have hsum (a : Fin r → Γ(X, V)) (j : Fin r) :
      dualApp (Fintype.linearCombination Γ(X, V) (fun i => resM (VB.dual E) h (d i)) a)
        le_rfl (resM E h (c.e j)) = a j := by
    rw [Fintype.linearCombination_apply]
    apply dualApp_chart_sum c h
    intro i j
    rw [dualApp_res]
    rfl
  refine ⟨fun a a' e => funext fun j => ?_, fun l => ?_⟩
  · rw [← hsum a j, ← hsum a' j, e]
  · refine ⟨fun j => dualApp l le_rfl (resM E h (c.e j)), ?_⟩
    exact c.isFrame.dual_ext h fun j => hsum _ j

def map {E' : X.Modules} (φ : E ≅ E') : Chart E' r := ⟨c.U, _, c.isFrame.map_iso φ.hom⟩

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

end CxPts

@[ext] structure Met (p : X ⟶ Sp k) (σ : k →+* ℂ) (E : X.Modules) (r : ℕ) where

  isVB : IsVB E r

  G : Chart E r → CxPts p σ → Matrix (Fin r) (Fin r) ℂ

  posDef : ∀ c y, y ∈ ptsIn p σ c.U → (G c y).PosDef

  trans : ∀ c c' y, y ∈ ptsIn p σ c.U → G c' y = chg (c.tr p σ c' y) (G c y)

def VB.IsVB.pick {E : X.Modules} {r : ℕ} (h : IsVB E r) (y : CxPts p σ) : Chart E r :=
  CxPts.pick h.isLB_det y

namespace Met

variable {E E' : X.Modules} {r : ℕ} (h : Met p σ E r) {V W : X.Opens} {y : CxPts p σ}

def form (s t : Γ(E, V)) (y : CxPts p σ) : ℂ :=
  HermFrame.form (h.G (h.isVB.pick y) y) ((h.isVB.pick y).crd p σ s y) ((h.isVB.pick y).crd p σ t y)

def ofPt (hE : IsVB E r) (c : CxPts p σ → Chart E r) (hc : ∀ y, y ∈ ptsIn p σ (c y).U)
    (H : CxPts p σ → Matrix (Fin r) (Fin r) ℂ) (hH : ∀ y, (H y).PosDef) : Met p σ E r where
  isVB := hE
  G c' y := chg ((c y).tr p σ c' y) (H y)
  posDef c' y hy := posDef_chg ((c y).isUnit_tr c' (hc y) hy) (hH y)
  trans c' c'' y hy := by rw [chg_chg, (c y).tr_mul' c' c'' hy]

def ofCover (hE : IsVB E r) {ι : Sort*} (c : ι → Chart E r)
    (hc : ∀ y : CxPts p σ, ∃ i, y ∈ ptsIn p σ (c i).U)
    (H : ι → CxPts p σ → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ i y, y ∈ ptsIn p σ (c i).U → (H i y).PosDef) : Met p σ E r :=
  ofPt hE (fun y => c (hc y).choose) (fun y => (hc y).choose_spec) (fun y => H (hc y).choose y)
    fun y => hH _ y (hc y).choose_spec

def IsCInf : Prop := ∀ (c : Chart E r), ∀ y ∈ ptsIn p σ c.U, MInfAt (h.G c) y

def IsConj (h' : Met p σ' E r) : Prop :=
  ∀ (c : Chart E r) (y : CxPts p σ) (y' : CxPts p σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 →
    h'.G c y' = (h.G c y).map star

def pull {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) :
    Met q σ ((Scheme.Modules.pullback π).obj E) r :=
  ofCover (h.isVB.pullback π) (fun c : Chart E r => c.pull h.isVB π)
    (fun z => ⟨_, h.isVB.mem_pick (PtsOver.map π hπ _ z)⟩)
    (fun c z => h.G c (PtsOver.map π hπ _ z)) fun c _ hz => h.posDef c _ hz

def dual : Met p σ (VB.dual E) r :=
  ofCover h.isVB.dual Chart.dual (fun y => ⟨_, h.isVB.mem_pick y⟩)
    (fun c y => dualGram (h.G c y)) fun c y hy => posDef_dualGram (h.posDef c y hy)

def map (φ : E ≅ E') : Met p σ E' r :=
  ofCover (h.isVB.of_iso φ) (·.map φ) (fun y => ⟨_, h.isVB.mem_pick y⟩) h.G h.posDef

def detWeight : Weight p σ (det E r) where
  isLB := h.isVB.isLB_det
  φ c y := -Real.log (h.G c y).det.re
  trans c c' y hy hy' := by
    have := gv_ne_zero (B := det E r) hy hy'
    rw [h.trans c c' y hy, det_chg, c.det_tr c' hy hy', Complex.re_ofReal_mul,
      Real.log_mul (by positivity) (det_re_pos (h.posDef c y hy)).ne']
    ring

variable {h}

end Met

@[ext] structure VMetric (p : X ⟶ Sp k) (E : X.Modules) (r : ℕ) where

  isVB : IsVB E r

  met : ∀ σ : k →+* ℂ, Met p σ E r

  conj : ∀ σ σ', (met σ).IsConj (met σ')

namespace VMetric

variable {E E' E₁ E₂ : X.Modules} {r r₁ r₂ : ℕ} (h : VMetric p E r)

def IsCInf : Prop := ∀ σ, (h.met σ).IsCInf

def pull {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) :
    VMetric q ((Scheme.Modules.pullback π).obj E) r :=
  ⟨h.isVB.pullback π, fun σ => (h.met σ).pull π hπ, fun σ σ' => (h.conj σ σ').pull π hπ⟩

def dual : VMetric p (VB.dual E) r :=
  ⟨h.isVB.dual, fun σ => (h.met σ).dual, fun σ σ' => (h.conj σ σ').dual⟩

def map (φ : E ≅ E') : VMetric p E' r :=
  ⟨h.isVB.of_iso φ, fun σ => (h.met σ).map φ, fun σ σ' => (h.conj σ σ').map φ⟩

def IsIsometry (h' : VMetric p E' r) (φ : E ≅ E') : Prop :=
  ∀ σ (V : X.Opens) (s t : Γ(E, V)), ∀ y ∈ ptsIn p σ V,
    (h'.met σ).form (φ.hom.app V s) (φ.hom.app V t) y = (h.met σ).form s t y

variable {h}

def det (H : h.IsCInf) : HermLB p where
  B := VB.det E r
  isLB := h.isVB.isLB_det
  φ σ := (h.met σ).detWeight
  cInf σ := (H σ).detWeight
  conj σ σ' := (h.conj σ σ').detWeight

end VMetric

structure HermVB (p : X ⟶ Sp k) (r : ℕ) where

  E : X.Modules

  h : VMetric p E r

  cInf : h.IsCInf

namespace HermVB

variable {r : ℕ} (E : HermVB p r)

def pull {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) : HermVB q r :=
  ⟨_, E.h.pull π hπ, E.cInf.pull π hπ⟩

def dual : HermVB p r := ⟨_, E.h.dual, E.cInf.dual⟩

def det : HermLB p := VMetric.det E.cInf

end HermVB

end GlobalTheory
