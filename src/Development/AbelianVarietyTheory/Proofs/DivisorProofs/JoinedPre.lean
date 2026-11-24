module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.CxCoh.CxMap

universe u u'

variable {C : Type u} [Category.{0} C] {C' : Type u'} [Category.{0} C'] {K : Cx C} {K' : Cx C'}

def pre (m : CxMap K K') {G : C' ⥤ C} (θ : G ⟶ m.G) : CxMap K K' where
  G := G
  a0 T := (m.a0 T).comp (K.M0.map (θ.app T))
  a1 T := (m.a1 T).comp (K.M1.map (θ.app T))
  a2 T := (m.a2 T).comp (K.M2.map (θ.app T))
  a3 T := (m.a3 T).comp (K.M3.map (θ.app T))
  compDegreeZero_natural {T T'} φ x := by
    change m.a0 T' (K.M0.map (θ.app T') (K.M0.map (G.map φ) x)) =
      K'.M0.map φ (m.a0 T (K.M0.map (θ.app T) x))
    rw [← K.M0.map_comp, θ.naturality, K.M0.map_comp, m.compDegreeZero_natural]
  compDegreeOne_natural {T T'} φ x := by
    change m.a1 T' (K.M1.map (θ.app T') (K.M1.map (G.map φ) x)) =
      K'.M1.map φ (m.a1 T (K.M1.map (θ.app T) x))
    rw [← K.M1.map_comp, θ.naturality, K.M1.map_comp, m.compDegreeOne_natural]
  compDegreeTwo_natural {T T'} φ x := by
    change m.a2 T' (K.M2.map (θ.app T') (K.M2.map (G.map φ) x)) =
      K'.M2.map φ (m.a2 T (K.M2.map (θ.app T) x))
    rw [← K.M2.map_comp, θ.naturality, K.M2.map_comp, m.compDegreeTwo_natural]
  comp_commutes_diffZero T x := by
    change m.a1 T (K.M1.map (θ.app T) (K.d0 _ x)) = K'.d0 T (m.a0 T (K.M0.map (θ.app T) x))
    rw [← K.diffZero_natural, m.comp_commutes_diffZero]
  comp_commutes_diffOne T x := by
    change m.a2 T (K.M2.map (θ.app T) (K.d1 _ x)) = K'.d1 T (m.a1 T (K.M1.map (θ.app T) x))
    rw [← K.diffOne_natural, m.comp_commutes_diffOne]
  comp_commutes_diffTwo T x := by
    change m.a3 T (K.M3.map (θ.app T) (K.d2 _ x)) = K'.d2 T (m.a2 T (K.M2.map (θ.app T) x))
    rw [← K.diffTwo_natural, m.comp_commutes_diffTwo]

theorem joined_pre (m : CxMap K K') {G : C' ⥤ C} (θ : G ⟶ m.G) : (m.pre θ).Joined m θ :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

end GlobalTheory.CxCoh.CxMap

namespace GlobalTheory.PDForm

def pairB {D D' : Data} (Λ' : Lift D') {σ : D.R →+* D'.R} (φ : D'.X ⟶ D.X) {φ₀ : D'.X₀ ⟶ D.X₀}
    (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) : CxMap (KK D.κ D.t) ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)) :=
  (morMap m).comp ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L))

end GlobalTheory.PDForm
