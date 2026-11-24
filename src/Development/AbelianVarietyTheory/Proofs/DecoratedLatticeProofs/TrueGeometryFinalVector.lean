module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.FamTraceChiCol


open GlobalTheory.StepData GlobalTheory.RootEx GlobalTheory.SymChain in
theorem conj_embX_toBlocks₂₂ {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL n k) :
    ((typeFrame ϖ ord).bas⁻¹ * embX c g * (typeFrame ϖ ord).bas).val.toBlocks₂₂ = 1 := by
  have e1 : (typeFrame ϖ ord).bas.val = fromBlocks 1 0 0 (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)).val := rfl
  have e2 : ((typeFrame ϖ ord).bas⁻¹).val =
      fromBlocks 1 0 0 ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val := by
    change (embA n _)⁻¹.val = _
    rw [← map_inv]; rfl
  rw [Units.val_mul, Units.val_mul, e1, e2, show (embX c g).val = fromBlocks g.val 0 0 1 from rfl,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₂, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
    Units.inv_mul]

end GlobalTheory.FamTraceChiCol

noncomputable section
namespace GlobalTheory.FamTraceChiCol


end GlobalTheory.FamTraceChiCol
end
