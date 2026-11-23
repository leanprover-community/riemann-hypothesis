module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGramPosSemidefAndNormAtPlace
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem datFramed_of_gram_posDef {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok)
    (hG : ∀ v : InfinitePlace K, (S.gramV.map v.embedding).PosDef) : DatFramed S h := by
  refine ⟨S.hDim h, (S.hB h).equivFun.symm, fun v => frameOf (GlobalTheory.PeriodClassSum.gramAt S h v),
    fun v => (frameOfSpec _ _ (GlobalTheory.PeriodClassSum.gramAt_posDef S h v (hG v))).1, fun v x => ?_⟩
  have h1 := (GlobalTheory.PeriodClassSum.isFormsOf_formsLat S h hG ⊥).2 v ((S.hB h).equivFun.symm x)
  have h2 : Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (S.hDim h))) (fun v => frameOf (GlobalTheory.PeriodClassSum.gramAt S h v)) v x =
      Formalism.HermitianLatticesTheory.normAt (S.hB h) (fun v => frameOf (GlobalTheory.PeriodClassSum.gramAt S h v)) v ((S.hB h).equivFun.symm x) := by
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    congr 2
    unfold Formalism.HermitianLatticesTheory.vecAt
    funext i
    simp only [Pi.basisFun_repr, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [h2]
  exact h1

theorem evGSD_datFramed : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (h : (evGSD W Ch sel mu P u).Ok), DatFramed (evGSD W Ch sel mu P u) h := by
  intro X _ Pr R W Ch sel Sg mu P u h
  refine datFramed_of_gram_posDef _ h fun v => ?_
  have e : (evGSD W Ch sel mu P u).gramV = GlobalTheory.TestLat.Compare.gramB X.K (W.lamTrue u R.m) := by
    ext i k
    show pairVr X.emb (W.lamTrue u R.m) 1 (bVV _ _ i) (bVV _ _ k) = _
    rw [GlobalTheory.ColNorms.pairVr_one_eq]
    exact GlobalTheory.PeriodClassSum.pairK_one_basis (W.lamTrue u R.m) i k
  rw [e]
  exact GlobalTheory.PeriodClassSum.gramB_posDef (W.lamTrue u R.m) v.embedding

end GlobalTheory.ColRows
