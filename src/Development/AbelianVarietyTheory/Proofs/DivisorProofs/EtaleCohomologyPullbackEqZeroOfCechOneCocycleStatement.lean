module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

theorem _root_.GlobalTheory.T.etaleCohomologyPullback_eq_zero_of_cechOneCocycle :
    ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X)
      (s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F),
      cobd (R := R) (E := cech f) (n := 1) s = 0 →
      ∀ x : H R (sch.obj X) F ((1 : ℕ) : ℤ),
        IsCls (R := R) (E := cech f) (n := 1) s (pull R (cechAug f) F ((1 : ℕ) : ℤ) x) →
        pull R (sch.map f) F ((1 : ℕ) : ℤ) x = 0 := by
  intro R _ F Y X f s hs x hx
  have hc := congrArg (fun t => (free R).map ((cechDiag f).app (op ⦋2⦌)) ≫ t) hs
  simp only [cobd, Preadditive.comp_sum, Preadditive.comp_zsmul, ← Functor.map_comp_assoc,
    cechDiag_δ, comp_zero] at hc
  have hc' : ((free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s :
      (free R).obj ((sch.obj Y).obj (op ⦋2⦌)) ⟶ F) = 0 := by
    simpa [Fin.sum_univ_succ] using hc
  have hd : (free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s = 0 := hc'
  obtain ⟨z, hzClass, hz⟩ := hx
  rw [← cechDiag_aug f, pull_comp, ← hzClass]
  simp only [pull, HK.pull, HK.pre, cpre_mk]
  rw [← CohomologyClass.mk_zero]
  apply congrArg CohomologyClass.mk
  apply Cocycle.ext
  change (Cochain.ofHom ((chains R).map (cechDiag f))).comp z.1 (zero_add _) = 0
  rw [hz, ClsBasic.ofHom_comp_single]
  simp only [← Category.assoc, ClsBasic.chainsXIso_nat]
  simp [Category.assoc, hd]
