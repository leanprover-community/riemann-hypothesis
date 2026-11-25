module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
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
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.Cyc.Model

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial

variable {l : ℕ} [Fact l.Prime]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.isom_gal (g : _root_.Formalism.BasicNotions.Loc.GQ l) :
    Isometry (g : _root_.Formalism.BasicNotions.Loc.Om l →+* _root_.Formalism.BasicNotions.Loc.Om l) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x => ?_
  change spectralNorm ℚ_[l] (PadicAlgCl l) (g x) = spectralNorm ℚ_[l] (PadicAlgCl l) x
  exact (spectralNorm_eq_of_equiv g x).symm

def extHom (g : GQ l) : PadicComplex l →+* PadicComplex l :=
  UniformSpace.Completion.mapRingHom (g : Om l →+* Om l) (isom_gal g).continuous

theorem extHom_coe (g : GQ l) (x : Om l) : extHom g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem extHom_cont (g : GQ l) : Continuous (extHom g) := UniformSpace.Completion.continuous_map

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.extHom_mul (g h : _root_.Formalism.BasicNotions.Loc.GQ l) (y : PadicComplex l) :
    _root_.GlobalTheory.Cyc.Model.extHom (g * h) y =
      _root_.GlobalTheory.Cyc.Model.extHom g (_root_.GlobalTheory.Cyc.Model.extHom h y) := by
  refine UniformSpace.Completion.induction_on y (isClosed_eq (_root_.GlobalTheory.Cyc.Model.extHom_cont _)
    ((_root_.GlobalTheory.Cyc.Model.extHom_cont g).comp (_root_.GlobalTheory.Cyc.Model.extHom_cont h))) fun x => ?_
  rw [_root_.GlobalTheory.Cyc.Model.extHom_coe, _root_.GlobalTheory.Cyc.Model.extHom_coe, _root_.GlobalTheory.Cyc.Model.extHom_coe]; rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.extHom_one (y : PadicComplex l) :
    _root_.GlobalTheory.Cyc.Model.extHom (1 : _root_.Formalism.BasicNotions.Loc.GQ l) y = y := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (_root_.GlobalTheory.Cyc.Model.extHom_cont _) continuous_id) fun x => ?_
  rw [_root_.GlobalTheory.Cyc.Model.extHom_coe]; rfl

def actC : GQ l →* (PadicComplex l ≃+* PadicComplex l) where
  toFun g := { extHom g with
    invFun := extHom g⁻¹
    left_inv := fun y => by
      change extHom g⁻¹ (extHom g y) = y
      rw [← extHom_mul, inv_mul_cancel, extHom_one]
    right_inv := fun y => by
      change extHom g (extHom g⁻¹ y) = y
      rw [← extHom_mul, mul_inv_cancel, extHom_one] }
  map_one' := by ext y; exact extHom_one y
  map_mul' g h := by ext y; exact extHom_mul g h y

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem norm_cyc_extHom (g : _root_.Formalism.BasicNotions.Loc.GQ l) (y : PadicComplex l) :
    ‖_root_.GlobalTheory.Cyc.Model.extHom g y‖ = ‖y‖ := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_norm.comp (_root_.GlobalTheory.Cyc.Model.extHom_cont g)) continuous_norm) fun x => ?_
  rw [_root_.GlobalTheory.Cyc.Model.extHom_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact (_root_.GlobalTheory.Cyc.Model.isom_gal g).norm_map_of_map_zero (map_zero _) x

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.isActC_actC :
    _root_.GlobalTheory.Cyc.IsActC (_root_.GlobalTheory.Cyc.Model.actC (l := l)) :=
  ⟨fun g x => _root_.GlobalTheory.Cyc.Model.extHom_coe g x, fun g y => norm_cyc_extHom g y⟩

end GlobalTheory.Cyc.Model
