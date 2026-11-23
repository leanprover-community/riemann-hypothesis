module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DeepSubMulSecNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFormFamilyHypothesesChangedSecondNormStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SecNormOfNetIn
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin




theorem inputsR_of_inputsNet : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsNet large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → ∃ n : SecNorm B, InputsR large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) K H Ch Ah Cq Aq C2 A2 CR CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus := by
  intro D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus h
  obtain ⟨hB, G, Gc, PH, Prw, Pet, Pd, hN, hF, hP⟩ := h
  obtain ⟨n, h1, h2, h3⟩ := secNorm_of_netIn D B P j X large₂ K ka Pd hN
  obtain ⟨G', hF', hP'⟩ := GlobalTheory.T.exists_formFamilyHypotheses_changedSecondNorm D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus n G Gc PH Prw Pet
    Pd _ hF hP
  exact ⟨n, baseIn_secNorm D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus n hB, h1, h2,
    G', Gc, PH, Prw, Pet, Pd, h3, hF', hP'⟩

end GlobalTheory.FinalJoin
