module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

theorem conjH_conjH_inv' (a : GL (Fin n) (AE D)) (b : hermA D n) : conjH a (conjH a⁻¹ b) = b := by
  apply Subtype.ext
  change a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj a.1 = b.1
  have h1 : a.1 * (a⁻¹).1 = 1 := Units.mul_inv a
  have h2 : adj (a⁻¹).1 * adj a.1 = 1 := by
    rw [← adj_mul, h1]
    unfold adj
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  calc a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj a.1
      = (a.1 * (a⁻¹).1) * b.1 * (adj (a⁻¹).1 * adj a.1) := by simp only [mul_assoc]
    _ = b.1 := by rw [h1, h2, one_mul, mul_one]

theorem inv_cpow_neg' (x : ℝ≥0) {w : ℂ} (hw : w ≠ 0) : (((x : ℝ)⁻¹ : ℝ) : ℂ) ^ (-w) = npow x w := by
  unfold npow
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Complex.zero_cpow hw, Complex.zero_cpow (neg_ne_zero.2 hw)]
  · have hpos : (0 : ℝ) ≤ (x : ℝ) := x.2
    have harg : ((x : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hpos]
      exact Real.pi_ne_zero.symm
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]


theorem nu_conj {θ : InfFam D} (hRc : RealConj) (hθ : IsInfFam θ) (a : GL (Fin n) (AE D))
    (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (L L₁ L₂ : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hnu2 : ∀ v (b : hermA D n),
      PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L₁ v) (L₂ v) (PositivityTheory.SiegelWeilFormula.Gen.matV v (conjH a b).1) =
        PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L v) (L v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1)) (c : hermA D n) :
    PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lam L₁ L₂ (conjH a c).1 = PositivityTheory.SiegelWeilFormula.Gen.nuA θ (fun _ => 1) lam L L c.1 := by
  exact congrArg₂ (· * ·) (hRc D θ hθ n a c) (finprod_congr fun v => hnu2 v c)

end PositivityTheory.PfSWUS.SwMatch

end
