module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmGoodModelOfGlobalArtinReciprocity
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BundleBothPartsOfStandardKernelAndSixHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGenusOneFormalIsoOfUnramifiedGoodReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertThetaAdmissibilityOfComplexMultiplication
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntInertOfComplexMultiplicationCondition
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TorsionTaylorAlgebraicLatticeExistsOfCm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem servH_row_of_artin :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd)
      (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex),
      (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) →
      RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  intro hA Bd Q Lk ker hQ hE
  have h2 : Formalism.L2.Th1.CM.CM2 := GlobalTheory.Corev.CmTwoClosing.cmGoodModel_of_globalArtinReciprocity hA
  obtain ⟨hT, hG, hC⟩ := GlobalTheory.CurveThetaInert.torsionTaylorAlgebraic_latticeExists_of_cm h2
  exact GlobalTheory.T.bundle_bothParts_of_standardKernel_and_six_hypotheses hT hG hC (GlobalTheory.intInert_of_complexMultiplication_condition h2) (GlobalTheory.TwV.Lt.inert_theta_admissibility_of_complex_multiplication h2)
    (GlobalTheory.TwV.Lt.exists_genusOne_formal_iso_of_unramified_good_reduction h2) Q Lk ker hQ hE

end GlobalTheory.Svd
