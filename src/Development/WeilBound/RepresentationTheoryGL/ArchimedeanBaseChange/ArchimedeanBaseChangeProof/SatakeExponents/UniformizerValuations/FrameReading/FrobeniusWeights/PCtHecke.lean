module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FGLeaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePow
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PCtSat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PCtSatB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.HcHecke
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FG

theorem ctHecke_holds : CtHecke := by
  intro E _ _ _ n a b h w ν ϖ k hw hϖ hν
  have h0 : ϖ ≠ 0 := b_unif_ne_zero hϖ
  have hord : ordL ((Units.mk0 ϖ h0 : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [Units.val_mk0]; exact ordL_unif hϖ
  have hH := PositivityTheory.Rg.BcB.F.Fok.ctT_hecke E n a b h w ν (Units.mk0 ϖ h0) hw hord hν k
  rw [Units.val_mk0] at hH
  refine ⟨hH.1, fun y hy g => (hH.2 y hy g).2, ?_⟩
  have hm : ν (-1) = 1 := by
    apply hν
    have := ord_neg_one' (w := w)
    rwa [GlobalTheory.BCT.InertChar.ord_eq_ordL] at this
  rw [map_pow, hm, one_pow]

end PositivityTheory.Rg.BcB.F.FG

end
