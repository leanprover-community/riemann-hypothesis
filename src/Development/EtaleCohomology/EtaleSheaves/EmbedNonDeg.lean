module

public import Development.EtaleCohomology.EtaleSheaves.ChartsGeomVpaPf
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof
  LateralTheory.E.ChartsGeom_vpaPf

namespace LateralTheory.E.GeometricData

def rA {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (W : Z.Opens) : A →+* Γ(Z, W) :=
  (p.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

def NonDeg {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∃ (U V : Z.Opens) (s : Γ(Z, U)) (s' : Γ(Z, V)), IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ ∧
    Z.basicOpen s = U ⊓ V ∧ Z.basicOpen s' = U ⊓ V ∧ ((U ⊓ V : Z.Opens) : Set Z).Nonempty ∧
    Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
      Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1 ∧
    (Polynomial.eval₂RingHom (rA p U) s).IsIntegral ∧ (Polynomial.eval₂RingHom (rA p V) s').IsIntegral

def Concl {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ ChartData p B C t

def TopInt : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → (rA p ⊤).IsIntegral

def LineOpens : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z → IsAffineOpen (⊤ : Z.Opens) ∨ NonDeg p

def EmbedNonDeg : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IsIntegral Z → (rA p ⊤).IsIntegral → NonDeg p → Concl p

def EmbedAffine : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IsIntegral Z → (rA p ⊤).IsIntegral → IsAffineOpen (⊤ : Z.Opens) → Concl p

theorem GeoData_of (hT : TopInt) (hL : LineOpens) (hN : EmbedNonDeg) (hE : EmbedAffine) : GeoData := by
  intro A _ _ Z p hIL hZ
  have hI : IsIntegral Z := hZ.1
  have hTop := hT A p hIL
  rcases hL A p hIL hZ with h | h
  · exact hE A p hI hTop h
  · exact hN A p hI hTop h

end LateralTheory.E.GeometricData
