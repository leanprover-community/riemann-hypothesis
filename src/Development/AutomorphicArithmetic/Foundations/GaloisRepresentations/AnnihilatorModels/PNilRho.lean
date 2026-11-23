module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem nil_transfer {R S M W : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup W] [Module S W] (φ : R →+* S) (mk : M → W) (hzero : mk 0 = 0)
    (hadd : ∀ x y, mk (x + y) = mk x + mk y) (hsmul : ∀ (a : R) x, mk (a • x) = φ a • mk x)
    (hext : ∀ f g : End S W, (∀ x, f (mk x) = g (mk x)) → f = g)
    (T : End S W) (D : End R M) (hTD : ∀ x, T (mk x) = mk (D x)) (Q : Polynomial R)
    (hQ : IsNilpotent (Polynomial.aeval D Q)) : IsNilpotent (Polynomial.aeval T (Q.map φ)) := by
  obtain ⟨N, hN⟩ := hQ
  have hpow : ∀ (n : ℕ) x, (T ^ n) (mk x) = mk ((D ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, hTD, ih]
  have key : ∀ (R' : Polynomial R) x,
      Polynomial.aeval T (R'.map φ) (mk x) = mk (Polynomial.aeval D R' x) := by
    intro R' x
    induction R' using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hq, hadd]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        End.mul_apply, End.mul_apply, hpow, Module.algebraMap_end_apply,
        Module.algebraMap_end_apply, hsmul]
  refine ⟨N, hext _ _ fun x => ?_⟩
  rw [← map_pow, ← Polynomial.map_pow, key, map_pow, hN]
  simp [hzero]

theorem UpperTheory.Gal.crystallineComparison.nilRho_of :
    NilRho := by
  intro l _ P ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj LL V _ _ _ _ _ ρ hV Q g
  haveI := hV.finite
  exact nil_transfer (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (wdMk P ι ρ) (wdMk_zero P ι ρ)
    (wdMk_add P ι ρ) (wdMk_smul P ι ρ) (fun _ _ => wd_ext P ι ρ) _ _
    (wdRho_mk P ι Bw h hj ρ g) Q
