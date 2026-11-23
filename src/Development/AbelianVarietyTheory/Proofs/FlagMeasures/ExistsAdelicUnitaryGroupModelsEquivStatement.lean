module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryGroupModelsEquiv
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

theorem _root_.GlobalTheory.T.exists_adelic_unitaryGroup_models_equiv : ∀ I : AutInst, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt I.F I.E I.cm.sig ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND I.cm.sig I.J ∧ ∃ T : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ≃ₜ* I.GA, (∀ h, (show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J from h) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ↔ T h ∈ I.GFset) ∧ (∀ h, I.fmat (T h).2 = (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _)) ∧ ∀ v θ, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ → ∀ h, uMat ((T h).1 v) = (I.P v)⁻¹ * Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θ h * I.P v := by
  first | exact @GlobalTheory.AdelicModels.exists_adelic_equiv | exact GlobalTheory.AdelicModels.exists_adelic_equiv | (intros; apply GlobalTheory.AdelicModels.exists_adelic_equiv <;> assumption)
