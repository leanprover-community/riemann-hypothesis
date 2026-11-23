module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionMultiplicative
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Mathlib.Tactic.ENatToNat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TranslateEq

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
open scoped TensorProduct

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt x ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (x.appTop.hom s) := by
  have hle : x.appLE ⊤ ⊤ le_top = x.appTop := by
    simp only [Scheme.Hom.appLE]
    exact Category.comp_id _
  simp only [valAt]
  rw [hle]

theorem chart_sep [Finite T] (Γ : QFGroup R T) (B : Type) [CommRing B] [Algebra R B]
    (c : Spec (CommRingCat.of B) ⟶ Γ.G.left) [IsOpenImmersion c]
    (hc : c ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ (I : Type) (_ : Finite I) (τ : I → T) (e : I → B →ₐ[R] FractionRing R),
      (∀ i, Spec.map (CommRingCat.ofHom (e i).toRingHom) ≫ c = (Γ.pt (τ i)).left) ∧
      ∀ b, (∀ i, e i b = 0) → b = 0 := by
  apply GlobalTheory.CompanionTheory.Ar.BT.CharMul.chart_sep <;> assumption

theorem sec_zero [Finite T] (Γ : QFGroup R T) (s : Γ(Γ.G.left, ⊤))
    (hs : ∀ t, valAt (Γ.pt t).left ⊤ le_top s = 0) : s = 0 := by
  let 𝒰 := Γ.G.left.affineOpenCover
  refine Scheme.OpenCover.ext_elem s 0 𝒰.openCover fun k => ?_
  rw [map_zero]
  let c : Spec (CommRingCat.of (𝒰.X k)) ⟶ Γ.G.left := 𝒰.f k
  haveI : IsOpenImmersion c := 𝒰.openCover.map_prop k
  letI : Algebra R (𝒰.X k) := (Spec.preimage (c ≫ Γ.G.hom)).hom.toAlgebra
  obtain ⟨I, _, τ, e, he, hi⟩ := chart_sep Γ (𝒰.X k) c (Spec.map_preimage (c ≫ Γ.G.hom)).symm
  have h0 := hi ((Scheme.ΓSpecIso (CommRingCat.of (𝒰.X k))).hom (c.appTop s)) fun i => by
    have h1 := hs (τ i)
    rw [← he i, valAt_top, Scheme.Hom.comp_appTop] at h1
    exact (congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (e i).toRingHom)) (c.appTop s))).symm.trans h1
  have h2 := congr((Scheme.ΓSpecIso (CommRingCat.of (𝒰.X k))).inv $h0)
  rw [Iso.hom_inv_id_apply, map_zero] at h2
  exact h2

def pullSec {A : Type} [CommRing A] {X : Scheme.{0}} (j : X ⟶ Spec (CommRingCat.of A)) (f : A) : Γ(X, ⊤) :=
  j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom f)

theorem valAt_sub' {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (a b : Γ(X, ⊤)) : valAt x ⊤ le_top (a - b) = valAt x ⊤ le_top a - valAt x ⊤ le_top b := by
  simp only [valAt_top, map_sub]

theorem valAt_mul {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valAt x U h (a * b) = valAt x U h a * valAt x U h b := by
  simp [valAt]

section Omega

variable (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (N : ℕ)


end Omega


end GlobalTheory.CompanionTheory.Ar.BT.TranslateEq
