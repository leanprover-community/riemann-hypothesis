module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTranspStatement
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

open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory

theorem galoisRepOfPolarizedCuspidal_iff_pair : GlobalTheory.Published.GelfandKazhdanDual →
    (GlobalTheory.Published.CaraianiLocalGlobalDual → GlobalTheory.Published.CaraianiLocalGlobal) ∧
    (GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) := by
  intro hGK
  refine ⟨fun hC => ?_, fun hP => ?_⟩
  · intro E Ω _ _ _ _ _ _ l _ ι a ha π hcsd hcoh
    have hd : DualIsConj π :=
      (dualIsConjBy_one π).1 (GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π 1 (hGK E a _) ((GlobalTheory.GalOfCusp.isConjDualBy_one π).2 hcsd))
    exact hC E Ω l ι a ha π hd hcoh
  · intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hpol
    exact hP E Ω l ι a ha π χ hr
      ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E χ) (hGK E a _) hpol.dual⟩

end GlobalTheory
