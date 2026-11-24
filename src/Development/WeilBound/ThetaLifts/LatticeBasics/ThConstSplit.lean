module

public import Development.WeilBound.ThetaLifts.LatticeBasics.ThConstInv
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LmOfLinBar
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
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

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem splitModel_of (h : PositivityTheory.KCo.DictX) : SplitModel := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' p v t
  obtain ⟨⟨ι, hι⟩, -, s2, k⟩ := h F E σ n d B X W M om χX χW p.base ⟨_, _, p.herm⟩ ⟨_, _, p.skew⟩ p.weil v t
  exact ⟨s2, ι, hι.bij, fun g hg => ⟨Matrix.GeneralLinearGroup.map (piW t) g.1, (k ι hι).1 g hg _ rfl⟩, (k ι hι).2⟩

theorem splitModel : SplitModel := splitModel_of PositivityTheory.KCo.dictionary_extended

end GlobalTheory.ThK.Dbl.TC

end
