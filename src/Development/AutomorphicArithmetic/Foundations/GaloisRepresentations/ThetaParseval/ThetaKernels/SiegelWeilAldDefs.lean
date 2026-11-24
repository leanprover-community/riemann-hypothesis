module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
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



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def SignOK_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (Y : Spc F E n) : Prop :=
  d.A.IsHerm σ d.B d.r d.s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ d.A.IsSkew σ d.B d.r d.s ∧ ∀ i j, σ (Y.J j i) = Y.J i j
def IsJ_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G) : Prop :=
  Continuous j ∧
  (∀ g, (inFrame d.b (j g)).submatrix (Sum.map (em0 h) (em0 h)) (Sum.map (em0 h) (em0 h)) = inFrame b g) ∧
  ∀ g, ∀ u ∈ ({Sum.inl (i0 h), Sum.inr (i0 h)} : Set (Fin d.n ⊕ Fin d.n)), ∀ v,
    inFrame d.b (j g) u v = (1 : Matrix _ _ (AE F E)) u v ∧ inFrame d.b (j g) v u = (1 : Matrix _ _ (AE F E)) v u
def Res_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G) {κ : Type}
    [Fintype κ] (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ Φ ∈ d.sch, ∀ Φ' ∈ schA F κ,
    (∀ X : Mx F E d.m d.n, (∀ a, X a (i0 h) = 0) → Tof d.B.ψ dd l b Φ' (X.submatrix id (em0 h)) = d.T Φ X) →
    ∀ g (X : Mx F E d.m d.n), (∀ a, X a (i0 h) = 0) → Tof d.B.ψ dd l b (om g Φ') (X.submatrix id (em0 h)) = d.T (d.om (j g) Φ) X
end PositivityTheory.SiegelWeilFormula.Ald
end
end
