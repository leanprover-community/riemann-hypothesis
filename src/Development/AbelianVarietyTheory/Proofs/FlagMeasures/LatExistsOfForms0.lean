module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LatExistsOfSteps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsotropicOrthHyp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveVectorNormNegHyperbolicPairStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.St.Lat

theorem latExists_of_forms0 : ∀ D : D7, Formalism.L2.Forms.Forms0 D D.u₀ → LatExists D := by
  intro D hF
  refine GlobalTheory.St.Lat.latExists_of ?_ ?_ D ?_
  · exact GlobalTheory.T.exists_primitive_vector_norm_neg_hyperbolicPair
  · exact GlobalTheory.unramified_degree_one_of_ncard_placesOver
  · exact GlobalTheory.IsoOrthHyp.exists_isotropic_orth_hyp D hF

end GlobalTheory.St.Lat
