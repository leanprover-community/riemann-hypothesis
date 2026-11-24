module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}

def InN (κ : DividedPowers I) {s : X ⟶ Sp R} (T : Thick (dp0 R) s) : Prop :=
  ∃ δ' : DividedPowers (T.J ⊔ I.map (algebraMap R T.B)),
    IsDPMorphism T.δ δ' (RingHom.id T.B) ∧ IsDPMorphism κ δ' (algebraMap R T.B)

def IsChart (s : X ⟶ Sp R) (U : X.affineOpens) : Prop :=
  Module.Flat R (Sec s U.1) ∧
    ∃ (d : ℕ) (t : MvPolynomial (Fin d) R →ₐ[R] Sec s U.1), t.toRingHom.FormallyEtale

abbrev Chart (s : X ⟶ Sp R) : Type := {U : X.affineOpens // IsChart s U}

abbrev bas (s : X ⟶ Sp R) (U : X.affineOpens) : Thick (dp0 R) s :=
  Thick.triv (Sec s U.1) (affPt s U) (affPt_w s U)

structure Tag (γ : DividedPowers I) (s : X ⟶ Sp R) {K : Type} (U : K → X.Opens) : Type 1 where

  T : Thick γ s

  k : K
  le : ⊤ ≤ T.x ⁻¹ᵁ U k

variable {γ : DividedPowers I} {s : X ⟶ Sp R} {K : Type} {U : K → X.Opens}

@[ext] structure Tag.Hom (S T : Tag γ s U) where

  f : S.T ⟶ T.T
  le : U S.k ≤ U T.k

instance : Category (Tag γ s U) where
  Hom := Tag.Hom
  id S := ⟨𝟙 _, le_rfl⟩
  comp f g := ⟨f.f ≫ g.f, f.le.trans g.le⟩
  id_comp _ := Tag.Hom.ext (Category.id_comp _)
  comp_id _ := Tag.Hom.ext (Category.comp_id _)
  assoc _ _ _ := Tag.Hom.ext (Category.assoc _ _ _)

def Tag.forget (γ : DividedPowers I) (s : X ⟶ Sp R) (U : K → X.Opens) : Tag γ s U ⥤ Thick γ s where
  obj S := S.T
  map f := f.f

end FubiniStudyChowHeightFormula₂.Adr
