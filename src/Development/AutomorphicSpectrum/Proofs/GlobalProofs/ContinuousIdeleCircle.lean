module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import GroundTheory.GlobalFields.TateThesis.HeckeChar
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps

namespace GlobalTheory.CompanionTheory.HeckeBridge

variable {E : Type} [Field E] [NumberField E]

def ideleCircle (χ : HChar E) (hu : IsUnitary χ) : GroundTheory.Global.IdeleGroup E →* Circle where
  toFun x := ⟨((χ.1 x : ℂˣ) : ℂ), by simp [Submonoid.unitSphere, hu x]⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Units.val_mul]
    rfl

theorem continuous_ideleCircle (χ : HChar E) (hu : IsUnitary χ) : Continuous (ideleCircle χ hu) :=
  Continuous.subtype_mk (Units.continuous_val.comp χ.2.1) _

def toHecke (χ : HChar E) (hu : IsUnitary χ) : GroundTheory.Global.HeckeCharacter E where
  toMonoidHom := QuotientGroup.lift (GroundTheory.Global.IdeleGroup.diagonal E).range (ideleCircle χ hu) (by
    rintro _ ⟨k, rfl⟩
    rw [MonoidHom.mem_ker]
    ext
    have := χ.2.2 k
    show ((χ.1 (Neutral.B1.diagUnits E k) : ℂˣ) : ℂ) = 1
    rw [this]; rfl)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk (GroundTheory.Global.IdeleGroup.diagonal E).range).continuous_iff.2
    (continuous_ideleCircle χ hu)

theorem coe_toIdele (χ : HChar E) (hu : IsUnitary χ) (x : GroundTheory.Global.IdeleGroup E) :
    (((toHecke χ hu).toIdele x : Circle) : ℂ) = ((χ.1 x : ℂˣ) : ℂ) := rfl

theorem coe_localComponent (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    (((toHecke χ hu).localComponent v x : Circle) : ℂ) = ((χ.loc v x : ℂˣ) : ℂ) := rfl

theorem toHecke_inv (χ : HChar E) (hu : IsUnitary χ) (hu' : IsUnitary χ⁻¹) : toHecke χ⁻¹ hu' = (toHecke χ hu)⁻¹ := by
  ext c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  show (((toHecke χ⁻¹ hu').toIdele x : Circle) : ℂ) = ((((toHecke χ hu).toIdele x)⁻¹ : Circle) : ℂ)
  rw [coe_toIdele, Circle.coe_inv, coe_toIdele]
  exact Units.val_inv_eq_inv_val (χ.1 x)

end GlobalTheory.CompanionTheory.HeckeBridge
