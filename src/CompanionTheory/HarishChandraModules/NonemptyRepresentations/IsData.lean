module

public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix

noncomputable section

namespace CompanionTheory.D.Inhab.IsDataInh

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

theorem glev_last_eq (k r : ℕ) : Glev k r (Fin.last r) = B2.UWb k r := by
  ext g
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun a => h2 a (by simp)⟩, fun ⟨h1, h2⟩ => ⟨h1, fun a _ => h2 a⟩⟩

theorem haar_glev_last (k r : ℕ) : ∃ μ : Measure (Mt k r), B.IsHaarOn (Glev k r (Fin.last r)) μ := by
  rw [glev_last_eq]
  exact Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r

theorem isData_of_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (hP : IsPlace P z z' π π') (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (l0 : ℕ) :
    ∃ (X : ActualOps P.k P.r z z' π π') (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
      (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))), IsData P z z' π π' X μ L st l0 := by
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P z z' π π' hP
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual Wp Wq P z z' π π' hP X l0
  exact ⟨X, L, st, hP, hμ, h1, h2, h3, h4, h5, h6⟩

end CompanionTheory.D.Inhab.IsDataInh
