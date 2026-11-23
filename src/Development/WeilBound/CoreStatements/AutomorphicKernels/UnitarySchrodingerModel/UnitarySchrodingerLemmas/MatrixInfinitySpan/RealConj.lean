module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussMulUnitary
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwSpan

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS.SwMatch

theorem matInf_map {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (X : Mx D n n) :
    (PositivityTheory.SiegelWeilFormula.Gen.matInf X).map (θ τ) = compAt θ τ X := by
  ext i j
  rfl

theorem aTau_val {D : D7} (θ : InfFam D) {n : ℕ} (a : GL (Fin n) (AE D)) (τ : D.what₂.Tau) :
    (aTau θ a τ).1 = compAt θ τ a.1 := rfl

theorem realConj : RealConj := by
  intro D θ hθ n a b
  unfold PositivityTheory.SiegelWeilFormula.Gen.nuInf
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hA : ((aTau θ a τ)⁻¹).1 * compAt θ τ a.1 = 1 := by
    rw [← aTau_val, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hc : compAt θ τ (conjH a b).1 = compAt θ τ a.1 * compAt θ τ b.1 * (compAt θ τ a.1)ᴴ := by
    rw [← GlobalTheory.VacKInf.LeviFix.compAt_adj' hθ τ a.1]
    show (a.1 * b.1 * adj a.1).map ((θ τ).comp (infPart D)) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  have hB : ((aTau θ a τ)⁻¹).1 * (compAt θ τ a.1 * compAt θ τ b.1 * (compAt θ τ a.1)ᴴ) *
      (((aTau θ a τ)⁻¹).1)ᴴ = compAt θ τ b.1 := by
    calc _ = (((aTau θ a τ)⁻¹).1 * compAt θ τ a.1) * compAt θ τ b.1 *
          (((aTau θ a τ)⁻¹).1 * compAt θ τ a.1)ᴴ := by
            rw [Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
      _ = compAt θ τ b.1 := by rw [hA]; simp
  rw [matInf_map, matInf_map, hc, hB]
  simp

end PositivityTheory.PfSWUS.SwSpan
