module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteProjBundleModelCohomologyEquivProdFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open GlobalTheory.EtC.CupSpec GlobalTheory.EtC.DiscCoch in

theorem _root_.GlobalTheory.T.discrete_projBundleModel_cohomology_equiv_prod_fibre :
    ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ),
      ∃ e : CohomologyClass ((chains R).obj (disc.obj F)) (Jcx R q N I) n ≃+
          CohomologyClass ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n,
        ∀ (β : Cocycle ((chains R).obj (disc.obj F)) (Jcx R q N I) n)
          (γ : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n),
          (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), β.1.v (-(p : ℤ)) s h = 0) →
          (∀ (U : Scheme.{0}) (x : F.obj (op U)),
            ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n,
              ev (R := R) β.1 0 n (by simp) U x = Jsec c ∧
              ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + n = s) (V : Scheme.{0})
                (y : Sx (sch.obj U ⨯ fibQ q N) k V),
                ev (R := R) c k s hs V y =
                  ev (R := R) γ.1 k s hs V
                    (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y)) →
          e (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  apply _root_.GlobalTheory.EtC.DiscCoch.model <;> assumption
