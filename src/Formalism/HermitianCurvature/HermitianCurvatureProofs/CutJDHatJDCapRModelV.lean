module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapR
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem site_vector_eq_tensor_product (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (y : ℂ) (b : Fin 2) : Wd.v0 (MA.sites P (MA.DQ P)) y b = L.Tprod y b 0 := by
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have hT : (fun σ => Wd.Ts σ y) ∘ MA.siteA P (MA.DQ P) = L.Tl y := by
    funext l
    simp only [Function.comp_apply]
    unfold R.LevelData.Tl
    rw [hp, hc, hci]
    rfl
  unfold Wd.v0 MA.sites R.LevelData.Tprod
  rw [List.map_reverse, List.map_ofFn, hT]

theorem star_site_vector_eq_tensor (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (y : ℂ) (a : Fin 2) :
    star (Wd.v0 (MA.sites P (MA.DQ P)) y a) = L.Tvprod (starRingEnd ℂ y) a 0 := by
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL'
  have sp : ∀ l, star (L.p l) = -L.pb l := fun l => by
    rw [hp, hpb]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).pP l)) = -MA.sc P (MA.DQ P) ((MA.DQ P).pbP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc, Formalism.FourierDecayAlt.P.MAx3.F.star_pP]
    unfold MA.sc
    simp
  have sc : ∀ l, star (L.c l) = L.cb l := fun l => by
    rw [hc, hcb]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).cP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc]
    rfl
  have sci : ∀ l, star (L.ci l) = L.cbi l := fun l => by
    rw [hci, hcbi]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).ciP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbiP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc]
    rfl
  have h := congrArg (fun M => M 0 a) (Formalism.FourierDecayAlt.P.TLB.star_Tprod_gen L sp sc sci y)
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h
  rw [site_vector_eq_tensor_product P L hL y a]
  exact h

theorem mirror_residue_model_holds : JDRModelV := by
  intro P L hL y
  refine ⟨fun b => site_vector_eq_tensor_product P L hL (y : ℂ) b, fun a => ?_⟩
  rw [star_site_vector_eq_tensor P L hL (y : ℂ) a, Complex.conj_ofReal]

end

end Formalism.FourierDecayAlt.P.CutMP
