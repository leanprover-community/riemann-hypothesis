module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqPowFrob
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

def galFq (g : GQ l) : Fq l a →+* Fq l a :=
  ((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) fun x => by
    rw [mem_resSub, RingHom.comp_apply, ← map_pow]
    exact congrArg (Per.σF g) (mem_resSub.1 x.2)

theorem val_galFq (g : GQ l) (x : Fq l a) : Fq.val l a (galFq l a g x) = Per.σF g (Fq.val l a x) := rfl

theorem exists_pow_eq (φ : Fq l a →+* Fq l a) : ∃ m : ℕ, ∀ x, φ x = x ^ l ^ m := by
  first
  | exact @_root_.GlobalTheory.FrobeniusPower.main
  | exact _root_.GlobalTheory.FrobeniusPower.main
  | (apply _root_.GlobalTheory.FrobeniusPower.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FrobeniusPower.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FrobeniusPower.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FrobeniusPower.main ..)
  | (intro h; exact _root_.GlobalTheory.FrobeniusPower.main h _ (fun _ => Iff.rfl))
  | exact _root_.GlobalTheory.FrobeniusPower.main ‹_› _ (fun _ => Iff.rfl)
  | (apply _root_.GlobalTheory.FrobeniusPower.main <;> first | assumption | exact fun _ => Iff.rfl)

theorem gal_wA_pow (g : GQ l) :
    ∃ s : ZMod a, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ s.val) w) := by
  obtain ⟨m, hm⟩ := exists_pow_eq l a (galFq l a g)
  refine ⟨(m : ZMod a), fun w => ?_⟩
  rw [ZMod.val_natCast, ← pow_eq_pow_mod m (sigma_pow_eq_one l a)]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff]
  change Per.σF g (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ m) w).coeff n)
  rw [coeff_sigma_pow, ← hm, val_galFq]

end GlobalTheory.BKReal
