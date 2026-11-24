module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

namespace GlobalTheory.AdForm

def intVecSub (D : D7) (n : ℕ) : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E) where
  carrier := intVec D n
  add_mem' := fun {x y} hx hy k => (hx k).add (hy k)
  zero_mem' := fun _ => isIntegral_zero
  smul_mem' := fun c {x} hx k => by
    show IsIntegral ℤ ((c : D.host.E) * x k)
    exact c.2.mul (hx k)

theorem coe_intVecSub (D : D7) (n : ℕ) : ((intVecSub D n : Submodule _ _) : Set (Fin n → D.host.E)) = intVec D n := rfl

theorem stdHom_map_splitIdem : ∀ (D : D7) (S T : HSp D) (a : AE D), IsSplitIdem D a → ∀ u ∈ stdHom S T, u.map (fun x => a * x) ∈ stdHom S T := by
  intro D S T a ha u hu
  have h := Formalism.IndefR.Fin.latO_map_splitIdem S T (intVecSub D S.rank) (intVecSub D T.rank) ha
    (u := u) (by rw [coe_intVecSub, coe_intVecSub]; exact hu)
  rw [coe_intVecSub, coe_intVecSub] at h
  exact h

end GlobalTheory.AdForm
