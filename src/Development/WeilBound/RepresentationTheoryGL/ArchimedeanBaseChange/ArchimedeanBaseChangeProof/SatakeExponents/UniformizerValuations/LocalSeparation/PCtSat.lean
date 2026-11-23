module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePow
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ordL_unif {w : Pl E} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) : ordL ϖ = 1 := by
  have h1 : Valued.v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.coe_ne_zero
  unfold ordL
  rw [dite_eq_right h1]
  have e : WithZero.unzero h1 = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, hϖ]
  rw [e, toAdd_ofAdd, neg_neg]

theorem ord_neg_one' {w : Pl E} : GlobalTheory.SmGL.ord (w.adicCompletion E) (-1) = 0 := by
  rw [GlobalTheory.BCT.InertChar.ord_eq_ordL]
  have : Valued.v ((((-1 : (w.adicCompletion E)ˣ)) : w.adicCompletion E)) = 1 := by simp
  have h1 : Valued.v ((((-1 : (w.adicCompletion E)ˣ)) : w.adicCompletion E)) ≠ 0 := by rw [this]; exact one_ne_zero
  unfold ordL
  rw [dite_eq_right h1]
  have e : WithZero.unzero h1 = 1 := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, this]; rfl
  rw [e, toAdd_one, neg_zero]

end PositivityTheory.Rg.BcB.F.RS
