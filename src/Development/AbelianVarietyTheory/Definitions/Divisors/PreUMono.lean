module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.AbCoh

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsAffineHom φ]

def preU (U : X.affineOpens) : X'.affineOpens := ⟨φ ⁻¹ᵁ U.1, U.2.preimage φ⟩

theorem preU_mono : Monotone (preU φ) := fun _ _ h _ hx ↦ h hx

def prePair (U : X.affineOpens) : Pair φ := ⟨(preU φ U, U), le_rfl⟩

def preAff : AffOp X ⥤ AffOp X' := (preU_mono φ).functor.op

abbrev OPre (s' : X' ⟶ Sp R') : AffOp X ⥤ CommAlgCat.{0} R' := preAff φ ⋙ OAff s'

def preRes (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OAff s') (OPre φ s') := CoefMap.restrict _ _

def preα (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (U : AffOp X) : (OAff s).obj U →+* (OPre φ s').obj U :=
  secPull s s' (prePair φ U.unop)

variable {φ} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}

def preCoef (h : φ ≫ s = s' ≫ spMap σ) : CoefMap σ (OAff s) (OPre φ s') where
  G := 𝟭 _
  α U := preα φ s s' U
  naturality {p q} a b := (pairPull h).naturality
    (homOfLE (show prePair φ q.unop ≤ prePair φ p.unop from
      ⟨preU_mono φ (leOfHom a.unop), leOfHom a.unop⟩)).op b
  smul U := semiHom_secPull h (prePair φ U.unop)

end GlobalTheory.AbCoh
