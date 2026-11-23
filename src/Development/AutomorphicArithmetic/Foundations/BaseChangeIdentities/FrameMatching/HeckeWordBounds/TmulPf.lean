module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.ChainSc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.DoubleSumFinprodFactor
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.tmul_pf :
    TMul := by
  intro E _ _ _ a b κ _ P _ L L' hL hL'
  refine ⟨fun X Y => ?_, FinConv.isTestFunction_mulConvolution hL.2 hL'.2⟩
  have hoff : IsTestP (fun w => mconv (L.ent P X X w) (L'.ent P Y Y w)) :=
    FinConv.isTestFunction_mulConvolution (hL.1 X X) (hL'.1 Y Y)
  refine Fm.isTestFunction_linearCombination (J := Option (Σ i : P, κ i))
    (fun j => j.elim (fun w => mconv (L.ent P X X w) (L'.ent P Y Y w))
      fun q w => mconv (L.ent P X (Function.update X q.1 q.2) w) (L'.ent P (Function.update X q.1 q.2) Y w))
    (fun j => ?_) _ (fun w => ?_) ?_
  · cases j with
    | none => exact hoff
    | some q => exact FinConv.isTestFunction_mulConvolution (hL.1 _ _) (hL'.1 _ _)
  · by_cases hw : w ∈ P
    · exact ⟨κ w, inferInstance, fun z => some ⟨⟨w, hw⟩, z⟩, fun _ => 1, by simp [LM.mul, LM.ent, hw]⟩
    · exact ⟨Unit, inferInstance, fun _ => none, fun _ => 1, by simp [LM.mul, LM.ent, hw]⟩
  · exact Fm.cof_off P hoff fun w hw => by simp [LM.mul, LM.ent, hw]

end
