module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfInterLwInterPoly
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

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.Proportionality

theorem hasChernIntegral_unique {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    {E : Fr (ratOf X) m 0} {O : X.X.Opens} {H : Mat m X.Fn → GlobalTheory.CxPts X.str σ → Mat m ℂ} {R : MvPolynomial (ι × ℕ) ℝ}
    {t t' : ℝ} (h : HasChernIntegral E O H R t) (h' : HasChernIntegral E O H R t') : t = t' :=
  h.2.symm.trans h'.2

theorem mumfordProportionality_of_goodChernWeil (h : GlobalTheory.Published.GoodChernWeil) : GlobalTheory.Published.MumfordProportionality := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k la
  obtain ⟨X, Eb, E', φ, f, Ob, Hm, hf, hg, hH, hG, hint⟩ := GlobalTheory.LieBase.exists_goodBase E H Dw l Xo c O β Y T F e σ U hσ hU Φ k
  obtain ⟨R, hR⟩ := GlobalTheory.AntisymmChern.antisymm_eq_chernRoots_mul_rootDiscr _ Dw.mult
    ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim)
  rw [GlobalTheory.Member.selfInter_Lw_interPoly (Φ.C k) la]
  have key := hasChernIntegral_unique (h.flag hf hg hH hG hR) (hint la R hR)
  convert key using 3 <;> exact Subsingleton.elim _ _

end GlobalTheory.Proportionality
