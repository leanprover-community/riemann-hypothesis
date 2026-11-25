module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExtensionOrderEqSpan
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSet
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSection
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFlat

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.FlatBC

section Alg

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']

def kapL (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    FractionRing R →ₗ[R] FractionRing R' where
  toFun := κ
  map_add' := map_add κ
  map_smul' r x := by
    have := congr($hκ r)
    simp only [RingHom.comp_apply] at this
    simp only [Algebra.smul_def, map_mul, RingHom.id_apply, this,
      IsScalarTower.algebraMap_apply R R' (FractionRing R')]

lemma inj_one (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    Function.Injective ((kapL κ hκ).liftBaseChange R') := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨r, d, hd, rfl⟩ := PositivityTheory.HtPt.Htat.ValuationInjectivePi.tensor_frac_form u
  rw [LinearMap.liftBaseChange_tmul] at hu
  have h1 : algebraMap R (FractionRing R) d ≠ 0 := by simpa using hd
  have h2 : κ (algebraMap R (FractionRing R) d)⁻¹ ≠ 0 :=
    (map_ne_zero κ).2 (inv_ne_zero h1)
  have h3 : r = 0 := by
    have h4 : algebraMap R' (FractionRing R') r * κ (algebraMap R (FractionRing R) d)⁻¹ = 0 := by
      rw [← Algebra.smul_def]; exact hu
    have := (mul_eq_zero.1 h4).resolve_right h2
    simpa using this
  simp [h3]

end Alg

section Sch

lemma top_le_pre {X Y : Scheme.{0}} (x : X ⟶ Y) : (⊤ : X.Opens) ≤ x ⁻¹ᵁ ⊤ := by simp

lemma valAt_map {A B : Type} [CommRing A] [CommRing B] (κ : A →+* B) {X : Scheme.{0}}
    (y : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ y) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ y) U h' s = κ (valAt y U h s) := by
  rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_comp _ y U ⊤ h (top_le_pre _), PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_spec]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

lemma valAt_const (Γ : QFGroup R T) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤) (h' : ⊤ ≤ Γ.G.hom ⁻¹ᵁ ⊤)
    (c : Γ(Spec (CommRingCat.of R), ⊤)) :
    valAt (Γ.pt t).left ⊤ h ((Γ.G.hom.appLE ⊤ ⊤ h').hom c) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) := by
  have e : (Γ.pt t).left ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    Over.w (Γ.pt t)
  rw [← PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_comp (Γ.pt t).left Γ.G.hom ⊤ ⊤ h' h (top_le_pre _), PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_congr e _ _ (top_le_pre _), PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_spec]

def secFn (Γ : QFGroup R T) : Submodule R (T → FractionRing R) where
  carrier := {f | ∃ s : Γ(Γ.G.left, ⊤), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤),
    valAt (Γ.pt t).left ⊤ h s = f t}
  add_mem' := by
    rintro f f' ⟨s, hs⟩ ⟨s', hs'⟩
    exact ⟨s + s', fun t h => by rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_add, hs, hs']; rfl⟩
  zero_mem' := ⟨0, fun t h => by rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_zero]; rfl⟩
  smul_mem' := by
    rintro r f ⟨s, hs⟩
    refine ⟨(Γ.G.hom.appLE ⊤ ⊤ (top_le_pre _)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * s,
      fun t h => ?_⟩
    rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_mul, valAt_const, hs]
    simp [Algebra.smul_def]

lemma mem_btOrder_iff [Finite T] (Γ : QFGroup R T) (f : T → R) :
    f ∈ Γ.btOrder ⊤ ↔ ∀ t, (fun h => algebraMap R (FractionRing R) (f (t * h))) ∈ secFn Γ := by
  have hmem : f ∈ Γ.btOrder ⊤ ↔ f ∈ Γ.btSet ⊤ :=
    mem_btOrder_iff_mem_btSet R T Γ ⊤ f
  rw [hmem]
  refine forall_congr' fun t => ?_
  have := _root_.GlobalTheory.CompanionTheory.Ar.BT.regularAt_forall_iff_exists_section R T Γ ⊤ (fun h => algebraMap R (FractionRing R) (f (t * h)))
  exact this

variable {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R']

theorem val_mem_span [Finite T] [Module.Flat R R'] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R'))
    (x : Γ(Γ'.G.left, ⊤)) :
    (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) x) ∈
      Submodule.span R' {w : T → FractionRing R' | ∃ n ∈ secFn Γ, w = fun h => κ (n h)} := by
  haveI := Γ.quasiCompact
  haveI := Γ.separated
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have H := hbc.cart
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) (top_le_pre _) (top_le_pre _)
    (by simp)).1 (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) (Γ.G.hom.isCompact_preimage (isAffineOpen_top _).isCompact)
      (Γ.G.hom.isQuasiSeparated_preimage (isAffineOpen_top _).isQuasiSeparated))
  refine PositivityTheory.HtPt.Htat.ValuationInjectivePi.pushout_induction po (fun y => (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) y) ∈
      Submodule.span R' {w : T → FractionRing R' | ∃ n ∈ secFn Γ, w = fun h => κ (n h)}) ?_ ?_ ?_ ?_ x
  · have : (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) (0 : Γ(Γ'.G.left, ⊤))) = 0 := by
      funext t; exact PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_zero _ _ _
    rw [this]
    exact Submodule.zero_mem _
  · intro s
    refine Submodule.subset_span ⟨fun t => valAt (Γ.pt t).left ⊤ (top_le_pre _) s, ⟨s, fun _ _ => rfl⟩, ?_⟩
    funext t
    rw [← PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_comp (Γ'.pt t).left F ⊤ ⊤ _ (top_le_pre _) (top_le_pre _),
      PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_congr (_root_.GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange R T Γ R' Γ' F hbc κ hκ t) _ _ (top_le_pre _),
      valAt_map κ _ _ (top_le_pre _)]
  · intro c n hn
    have : (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) (((Γ'.G.hom.appLE ⊤ ⊤ (top_le_pre _)).hom c) * n)) =
        ((Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom c) •
          (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) n) := by
      funext t
      rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_mul, valAt_const]
      simp [Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ hn
  · intro p q hp hq
    have : (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) (p + q)) =
        (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) p) + (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) q) := by
      funext t
      exact PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_add _ _ _ _ _
    rw [this]
    exact Submodule.add_mem _ hp hq

lemma btOrder_le_ext [Finite T] [Module.Flat R R'] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    Γ'.btOrder ⊤ ≤ extOrder (algebraMap R R') (Γ.btOrder ⊤) := by
  intro g hg
  rw [_root_.GlobalTheory.CompanionTheory.Ar.BT.ExtSpan.extOrder_eq_span]
  refine PositivityTheory.HtPt.Htat.ValuationInjectivePi.alg_core κ hκ (secFn Γ) (Subalgebra.toSubmodule (Γ.btOrder ⊤)) (fun f => mem_btOrder_iff Γ f) g ?_
  intro t
  obtain ⟨x, hx⟩ := (mem_btOrder_iff Γ' g).1 hg t
  have e : (fun h => algebraMap R' (FractionRing R') (g (t * h))) =
      fun h => valAt (Γ'.pt h).left ⊤ (top_le_pre _) x := by
    funext h
    exact (hx h _).symm
  rw [e]
  exact val_mem_span Γ Γ' F hbc κ hκ x

lemma ext_le_btOrder [Finite T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    extOrder (algebraMap R R') (Γ.btOrder ⊤) ≤ Γ'.btOrder ⊤ := by
  have hκ' : ∀ r, κ (algebraMap R _ r) = algebraMap R' (FractionRing R') (algebraMap R R' r) :=
    fun r => congr($hκ r)
  refine Algebra.adjoin_le ?_
  rintro _ ⟨f, hf, rfl⟩
  refine (mem_btOrder_iff Γ' _).2 fun t => ?_
  obtain ⟨s, hs⟩ := (mem_btOrder_iff Γ f).1 hf t
  refine ⟨(F.appLE ⊤ ⊤ (top_le_pre _)).hom s, fun h hh => ?_⟩
  rw [← PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_comp (Γ'.pt h).left F ⊤ ⊤ _ _ (top_le_pre _),
    PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_congr (_root_.GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange R T Γ R' Γ' F hbc κ hκ h) _ _ (top_le_pre _),
    valAt_map κ _ _ (top_le_pre _), hs h, hκ']

end Sch

theorem btOrder_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → Γ'.btOrder ⊤ = extOrder (algebraMap R R') (Γ.btOrder ⊤) :=
  PositivityTheory.HtPt.Htat.ValuationInjectivePi.btOrder_flat_baseChange

end GlobalTheory.CompanionTheory.Ar.BT.FlatBC
