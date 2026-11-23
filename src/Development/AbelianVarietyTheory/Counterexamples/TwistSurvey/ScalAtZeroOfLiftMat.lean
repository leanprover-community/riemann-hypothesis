module

public import Formalism.HermitianLattices.StatementMaj
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix

namespace GlobalTheory.ScalarConjugation

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links

section Abstract

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem maj_eq_zero {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K)
    (h : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) X v x x = 0) : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) X v x y = 0 := by
  have hc : ∀ i, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i = 0 := by
    have hs : ∑ i, ((Complex.normSq (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i) : ℝ) : ℂ) = 0 := by
      rw [← h]
      unfold Formalism.HermitianLatticesTheory.majAt
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    have hr : ∑ i, Complex.normSq (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i) = 0 := by
      exact_mod_cast hs
    intro i
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => Complex.normSq_nonneg _).1 hr i (Finset.mem_univ i))
  unfold Formalism.HermitianLatticesTheory.majAt
  exact Finset.sum_eq_zero fun i _ => by rw [hc i, star_zero, zero_mul]

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

end Abstract

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

end Concrete

section Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.MainNotions

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


end Comparison₂

end GlobalTheory.ScalarConjugation
