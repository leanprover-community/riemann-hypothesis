module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Matrix

namespace GlobalTheory.BotRealInv

theorem substF_minorF {D : D7} {a d a₁ d₁ : ℕ} {n : D.what₂.Tau → ℕ} (ha : a = a₁) (hd : d = d₁) (T : Tup D a d n)
    (H : D.what₂.Tau → Matrix (Fin a₁) (Fin a₁) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) (fun τ => (H τ)ᵀ) (GlobalTheory.BotFormula.minorF ha hd T) =
      (∏ τ, (H τ).det ^ n τ) • GlobalTheory.BotFormula.minorF ha hd T := by
  subst ha hd
  have e : GlobalTheory.BotFormula.minorF (rfl : a = a) (rfl : d = d) T = GlobalTheory.NormSum.minorPol D T := by
    unfold GlobalTheory.BotFormula.minorF
    exact MvPolynomial.rename_id_apply _
  rw [e]
  have one : ∀ (τ : D.what₂.Tau) (s : Fin a → Fin d),
      GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) (fun τ => (H τ)ᵀ)
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det =
      MvPolynomial.C (H τ).det *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det := by
    intro τ s
    rw [AlgHom.map_det, RingHom.map_det, ← Matrix.det_transpose ((MvPolynomial.C : ℂ →+* _).mapMatrix (H τ)), mul_comm,
      ← Matrix.det_mul]
    congr 1
    refine Matrix.ext fun i i' => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, GlobalTheory.CompactHowe.substF_X,
      RingHom.mapMatrix_apply, Matrix.transpose_apply]
    rw [Finset.sum_eq_single (s i)]
    · simp only [Matrix.one_apply_eq, one_mul]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [GlobalTheory.NormSum.minorPol, map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod]
  simp only [one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

theorem succ_mul_succ_sub_one_div_succ {G : Type*} [CommGroup G] (a e c : G) : a * e / (c * e) = a / c := mul_div_mul_right_eq_div _ _ _

end GlobalTheory.BotRealInv

end
