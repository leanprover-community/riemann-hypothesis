module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.BaseChangeIsobaricNOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.F.Rig

def SplitSatPre : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ D D' : Pre E n, {w | IsSplitAt w ∧ ¬ D.SplitAt π w}.Finite → {w | IsSplitAt w ∧ ¬ D'.SplitAt π w}.Finite →
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ D'.Sat w B

theorem csdAsc_of (h1 : Strings) (h2 : CuspCsd) {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (D : Pre E n)
    (hr : D.Reg) (ht : D.ThetaStable) (i : Fin D.c) : PositivityTheory.Rg.BcN.CsdAsc (D.V i) := by
  obtain ⟨a, d, P, ha, hd, hu, hn, he⟩ := h1 E n D hr i
  have e := he P (Setoid.refl (α := CuspSub E a) P)
  exact ⟨a, d, P, hu, hn, h2 E n D hr ht i a d P ha hd hu hn e, e⟩

end PositivityTheory.Rg.BcB.F.Rig

end
