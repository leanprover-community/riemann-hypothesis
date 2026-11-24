module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsPolFibreOfKeyPB
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormEqPiMulHermForm
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.CM.LieMetric

theorem vecLine_norm_sq_eq_form : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (h : HermFam K (Fin x.P.g → K)), (GenFib.mk x.P φ hf x.v x.basis : GenFib A).IsHerm h → ∀ (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ∀ s : K →+* ℂ, ℓ.n s ^ 2 = (h.form s (Pi.single i 1) (Pi.single i 1)).re := by
  intro hU hL K _ _ A x φ hf h H i ℓ hℓ s
  obtain ⟨xs, u, Hm, χ, W, hg, hpb, hA, hW, e⟩ := hℓ.2.2 s
  obtain ⟨ψ, hg', hψ, hv⟩ := GlobalTheory.KeyFibre.exists_isPolFibre_of_keyPB K ℂ s x xs hpb
  have hc : IsLieComb (Pi.single i 1) x.v (x.v i) :=
    (LieComb.isLieComb_iff_tanExp _ _).2 (LieComb.tanExp_single x.basis.1 i).symm
  have hv' : IsVecOver s ψ (x.v i) (xs.v (i.cast hg.symm)) := hv (i.cast hg.symm)
  have := form_eq_pi_mul_hermForm hU hL K A (GenFib.mk x.P φ hf x.v x.basis) h H s xs.P ψ u Hm χ hψ hA
    _ _ _ _ _ _ W W hc hc hv' hv' hW hW
  rw [e]
  refine Eq.trans ?_ (congrArg Complex.re this).symm
  rw [Complex.re_ofReal_mul]
  rfl

end GlobalTheory.CM.LieMetric
