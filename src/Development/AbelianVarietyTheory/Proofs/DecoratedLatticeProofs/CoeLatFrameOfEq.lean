module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical

open scoped ComplexOrder

namespace GlobalTheory.AdForm.VacStd

theorem coe_latFrame_of_eq {D : D7} (S : HSp D) (hs : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (h : S = Formalism.BasicNotions.Examples₂.posSpace hs N) :
    (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank := by
  subst h
  ext x
  show x ∈ GlobalTheory.PlaceModel.latFrame _ ↔ ∀ k, IsIntegral ℤ (x k)
  rw [GlobalTheory.PlaceModel.mem_latFrame]
  exact Formalism.IndefR.Seed.FrmC.stdLat_std hs N (fun _ => false) N 0 x

theorem gram_of_eq {D : D7} (S : HSp D) (hs : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (h : S = Formalism.BasicNotions.Examples₂.posSpace hs N) : S.gram = 1 := by
  subst h
  refine Matrix.ext fun a b => ?_
  exact (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs N (fun _ => false) N 0 a b).trans
    (by
      by_cases hab : a = b
      · subst hab
        rw [Matrix.one_apply_eq]
        exact (if_pos rfl).trans (by simp [Formalism.BasicNotions.Examples₂.sgn])
      · rw [Matrix.one_apply_ne hab]
        exact if_neg hab)

theorem cartan_of_gram {D : D7} {S : HSp D} (h : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have e : gramAt D S τ = 1 := by rw [gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e]
  exact ⟨Matrix.mul_one _, by simp, by rw [Matrix.mul_one]; exact Matrix.PosDef.one⟩

end GlobalTheory.AdForm.VacStd
