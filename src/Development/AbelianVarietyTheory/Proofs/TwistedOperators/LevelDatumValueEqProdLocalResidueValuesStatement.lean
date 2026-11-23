module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelDatumValueEqProdLocalResidueValues
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.levelDatumValue_eq_prod_localResidueValues : ∀ (D : D7) (a b : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (χ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Hl : ∀ PP : ↥L.Pg, Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP.1))) (cl : ∀ PP : ↥L.Pg, Hl PP →* ℂˣ),
    L.P = Formalism.L2.DIV.LevelP.ofLocal Hl cl →
    ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP),
      omegaG L χ y = ∏ PP : ↥L.Pg, gLoc L PP.1 (Hl PP) (cl PP) (χ PP.1) (y PP.1) := by
  first | exact @GlobalTheory.StepVec.omegaG_eq_prod_gLoc | exact GlobalTheory.StepVec.omegaG_eq_prod_gLoc | (intros; apply GlobalTheory.StepVec.omegaG_eq_prod_gLoc <;> assumption)
