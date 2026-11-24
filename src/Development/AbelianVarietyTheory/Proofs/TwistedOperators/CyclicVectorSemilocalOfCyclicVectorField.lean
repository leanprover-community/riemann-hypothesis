module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open GlobalTheory.RegSS Matrix

namespace GlobalTheory.RegSS.Semilocal


open Matrix in
theorem _root_.GlobalTheory.RegSS.Semilocal.krylov_map_ringHom {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n A) (v : n → A) :
    (_root_.GlobalTheory.RegSS.krylov M v).map f = _root_.GlobalTheory.RegSS.krylov (M.map f) (f ∘ v) := by
  ext i j
  simp only [_root_.GlobalTheory.RegSS.krylov, Matrix.map_apply, Matrix.of_apply, RingHom.map_mulVec]
  congr 2
  exact RingHom.map_pow f.mapMatrix M _


open Matrix in
theorem _root_.GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField :
    _root_.GlobalTheory.RegSS.CyclicField → _root_.GlobalTheory.RegSS.CyclicSemilocal := by
  intro hF A _ _ n _ _ M hM
  have hw : ∀ p : MaximalSpectrum A, ∃ w : n → A ⧸ p.asIdeal,
      IsUnit (_root_.GlobalTheory.RegSS.krylov (M.map (Ideal.Quotient.mk p.asIdeal)) w).det := by
    intro p
    haveI := p.isMaximal
    letI := Ideal.Quotient.field p.asIdeal
    exact hF _ n _ (by rw [Matrix.charpoly_map]; exact hM.map)
  choose w hw using hw
  have hcop : Pairwise (Function.onFun IsCoprime fun p : MaximalSpectrum A => p.asIdeal) :=
    fun p q hpq => Ideal.isCoprime_iff_sup_eq.mpr
      (p.isMaximal.coprime_of_ne q.isMaximal (mt MaximalSpectrum.ext hpq))
  have hs : ∀ y : ∀ p : MaximalSpectrum A, A ⧸ p.asIdeal,
      ∃ a : A, ∀ p, Ideal.Quotient.mk p.asIdeal a = y p := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.quotientInfToPiQuotient_surj hcop y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, fun p => by rw [← hx]; rfl⟩
  choose v hv using fun j => hs fun p => w p j
  refine ⟨v, ?_⟩
  by_contra h
  obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr h)
  let p : MaximalSpectrum A := ⟨I, hI⟩
  have hvp : (Ideal.Quotient.mk p.asIdeal) ∘ v = w p := funext fun j => hv j p
  have hzero : Ideal.Quotient.mk p.asIdeal (_root_.GlobalTheory.RegSS.krylov M v).det = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [RingHom.map_det, RingHom.mapMatrix_apply, _root_.GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hvp] at hzero
  haveI := p.isMaximal
  exact (hw p).ne_zero hzero

end GlobalTheory.RegSS.Semilocal
