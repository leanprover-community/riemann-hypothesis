module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstTermExistenceOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsDetUnipotentRadicalEqOneStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnipotentRadicalConjScalingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightInvariantHaarLeviStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureIwasawaModularCharacterStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSemidirectProductFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedUnipotentRadicalStabilizerStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalInfLeviTrivialStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalStabilizerPropertyStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

theorem modular_stab (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (GlobalTheory.RegSW.stab d)]
    (q : GlobalTheory.RegSW.stab d) :
    Measure.modularCharacterFun q = GlobalTheory.RegSW.absDet d q ^ (W.rank + t) := by
  haveI : LocallyCompactSpace (radN d) := (GlobalTheory.T.isClosed_unipotent_radical_stabilizer D B W t d).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (levM d) := (GlobalTheory.T.unipotent_radical_stabilizer_property D B W t d).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (GlobalTheory.RegSW.stab d) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨νN, h1, h2, h3⟩ := GlobalTheory.T.exists_haar_unipotent_radical_conj_scaling D B W t d
  obtain ⟨νM, h4, h5⟩ := GlobalTheory.T.exists_right_invariant_haar_levi D B W t d
  exact GlobalTheory.T.haar_measure_semidirect_product_formula (GlobalTheory.RegSW.stab d) (radN d) (levM d) (GlobalTheory.T.isClosed_unipotent_radical_stabilizer D B W t d) (GlobalTheory.T.unipotent_radical_stabilizer_property D B W t d)
    (exists_radN_mul_levM d) (GlobalTheory.T.unipotent_radical_inf_levi_trivial D B W t d)
    νN νM h1 h2 h4 h5 ((powMonoidHom (W.rank + t) : ℝ≥0 →* ℝ≥0).comp (GlobalTheory.RegSW.absDet d))
    (fun n hn => by simp [GlobalTheory.T.absDet_unipotent_radical_eq_one D B W t d n hn]) (fun m hm => by simpa using h3 m hm) q

theorem qk : PositivityTheory.Rg.Rsw.L.QK := by
  intro D t B W d l hl νK hνK s hs hlaw g
  obtain ⟨hIw, hK⟩ := GlobalTheory.RegSch.FirstTermCompare.hasIw_of_good d hl
  haveI : LocallyCompactSpace (GlobalTheory.RegSW.stab d) :=
    (GlobalTheory.RegSW.isClosed_stab d).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (GA D B) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D B μ inferInstance
  refine GlobalTheory.T.haar_measure_iwasawa_modular_character (GA D B) μ (GlobalTheory.RegSW.stab d) l.K (GlobalTheory.RegSW.isClosed_stab d) hK
    (fun g => ?_) ((powMonoidHom (W.rank + t) : ℝ≥0 →* ℝ≥0).comp (GlobalTheory.RegSW.absDet d))
    (show Continuous fun q => GlobalTheory.RegSW.absDet d q ^ (W.rank + t) from (GlobalTheory.RegSW.continuous_absDet d).pow _)
    (fun q => ?_) νK hνK s hs (fun q h => ?_) g
  · obtain ⟨q, k, hk, e⟩ := hIw g
    exact ⟨q, q.2, k, hk, e⟩
  · simpa using modular_stab D B W t d q
  · simpa using hlaw q h

end GlobalTheory.CompanionTheory.QKAvg
