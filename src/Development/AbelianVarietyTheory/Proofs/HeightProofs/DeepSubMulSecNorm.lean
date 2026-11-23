module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
public import Formalism.LocalToGlobal.ProjectiveLattices.XPlusWireT
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (n : SecNorm B)




theorem hypC_secNorm (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    HypC large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) H C2 A2 CR Bx CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S)
        ka wL wF T nP nW h0 nus ↔
      HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus := Iff.rfl




theorem deepSubMul_secNorm : DeepSubMul (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ↔ DeepSubMul X := Iff.rfl

end




theorem baseIn_secNorm : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (n : SecNorm B), BaseIn large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → BaseIn large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) K H Ch Ah Cq Aq C2 A2 CR CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus := by
  intro D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus n h
  obtain ⟨a1, a2, a3, a4, a5⟩ := h
  exact ⟨(hypC_secNorm X n large₂ H C2 A2 CR 0 CT S ka wL wF Tn nP nW h0 nus).2 a1,
    (latAt_N n.N n.h0 n.h1 n.h2 n.h3 n.h4).2 a2,
    (lamwAt_N n.N n.h0 n.h1 n.h2 n.h3 n.h4 large₂ K.CL K.AL).2 a3,
    fun hj => (qAt_N n.N n.h0 n.h1 n.h2 n.h3 n.h4 large₂ _ _ _ _ _ _ _ _).2 (a4 hj),
    (deepSubMul_secNorm X n).2 a5⟩

end GlobalTheory.FinalJoin
