module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemDecIsFrob
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIso
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.TwUnit

theorem isKsForm_and_unit : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j, 1 ≤ j → j ≤ D.R.m → (Y.S.A j).IsKsForm) ∧ ∀ i b P, P ∉ D.ntw.S0 i → ∃ u : (D.ntw.O i)ˣ, Y.H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u := by
  intro D X E Y
  refine ⟨fun j h1 h2 => ?_, fun i b P hP => ?_⟩
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
    exact GlobalTheory.isKsForm_of_formsIso _ _ (Y.YS.fi ⟨n, h2⟩) (X.integral ⟨n, h2⟩).1
  · obtain ⟨σ, -, hσ⟩ := GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)
    exact ⟨Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom
      (if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹), Y.del i b P hP σ hσ⟩

end GlobalTheory.TwUnit
