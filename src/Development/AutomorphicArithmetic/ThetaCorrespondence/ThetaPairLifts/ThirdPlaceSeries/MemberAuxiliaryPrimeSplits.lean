module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplitAll
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



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.SplitPrimeAuxiliary
open scoped Pointwise
theorem exists_auxiliary_prime_split_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ v, v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  intro _ hL
  apply StepW.of_all
  intro K B f T w _ _ _ P x _ v hv
  rcases hv with hv | hv
  · exact isSplitPl_of_split B.host B.host.pde_prime B.toPre.pde_split.1 v hv
  · exact isSplitPl_of_split B.host B.host.pde'_prime B.toPre.pde_split.2 v hv
end GlobalTheory.SplitPrimeAuxiliary
end
section

theorem _root_.GlobalTheory.T.places_over_pde_isSplitPl_of_levelC : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ v, v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  first | exact @_root_.GlobalTheory.SplitPrimeAuxiliary.exists_auxiliary_prime_split_alt | exact _root_.GlobalTheory.SplitPrimeAuxiliary.exists_auxiliary_prime_split_alt | (intros; apply _root_.GlobalTheory.SplitPrimeAuxiliary.exists_auxiliary_prime_split_alt <;> assumption)
end
end
