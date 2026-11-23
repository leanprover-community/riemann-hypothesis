module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryBijectiveOfLevelMatchStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIntoStepZeroFormsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIsometricOfRepresentativesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRepresentsClassesWeightOneStatement
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

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDictCore_holds : ∀ D : D7, ColDictCore D := by
  intro D
  unfold ColDictCore
  intro X u F Tr hK hLev hStab

  have hConj : ∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a) :=
    GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X Tr.ιA ⟨Tr.ιA_rat, Tr.ιA_int⟩
  refine ⟨(GlobalTheory.T.transport_represents_classes_weight_one D X u F Tr hK hConj hLev).1, GlobalTheory.T.columnDictionary_into_stepZeroForms D X u F Tr hK hConj hLev,
    GlobalTheory.T.columnDictionary_bijective_of_levelMatch D X u F Tr hK hConj hLev, ?_⟩
  intro what₂ cs hinj hReps
  exact GlobalTheory.T.columnDictionary_isometric_of_representatives D X u F Tr hK hConj hLev hStab what₂ cs hinj hReps

end GlobalTheory.St
