module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamLine

variable {D : D7}

def intRing (D : D7) : Subring (AE D) := (GlobalTheory.CharFin.hatRing D.host.F D.host.E).comap (finPart D)

theorem mem_intRing (z : AE D) : z ∈ intRing D ↔ finPart D z ∈ intAE D := by
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact Iff.rfl

theorem finPart_cA (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem cA_mem {z : AE D} (hz : z ∈ intRing D) : cA D z ∈ intRing D := by
  rw [mem_intRing] at hz ⊢
  rw [finPart_cA]
  have : intAE D ≤ (intAE D).comap (sigR (Af D.host.F) D.sp.cm.sig).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, rfl⟩
    exact AddSubgroup.subset_closure
      ⟨a, ha, RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E) x, rfl⟩
  exact this hz

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (p : SplitPt D k)

variable {p} {N : ℕ}

section Line

variable {S : HSp D} [Subsingleton (Fin S.rank)] (i : Fin S.rank)


end Line

end GlobalTheory.RamLine
