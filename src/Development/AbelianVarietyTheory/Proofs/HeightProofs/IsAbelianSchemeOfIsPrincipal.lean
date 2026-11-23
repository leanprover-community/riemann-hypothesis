module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
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
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CMCurveHermitianForms
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.EigenLatticeFibres

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory.CM GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section
namespace GlobalTheory.CMSharedCompare

section Comb

variable {R : Type} [CommRing R]

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

section Vec

variable {t : SAB H (Sp (𝓞 K))} (G : EigenLatticeFibres.GenFib t)

end Vec

structure Partner {T : PAT H (Sp (𝓞 K))} (F : GenFib T.pol) where

  tK : SAB H (Sp K)

  m : SABMap tK T.t (spMap (algebraMap (𝓞 K) K))

  v : Fin F.P₀.g → (epsR K ⟶ tK.G)
  basis : IsLieBasis v
  same : ∀ i, (v i).left ≫ m.φ = (F.v i).left ≫ F.φ

variable {T T' : PAT H (Sp (𝓞 K))}

namespace Partner

variable {F : GenFib T.pol} {F' : GenFib T'.pol} (Q : Partner F) (Q' : Partner F')

end Partner

section Metric

variable {T : PAT H (Sp (𝓞 K))} {F : GenFib T.pol} (Q : Partner F)

end Metric

section Embeddings

end Embeddings

section Isogeny

end Isogeny

section Object

theorem nonempty_genFib (P : Out.PolAV (Sp (𝓞 K))) : Nonempty (GenFib P) := by
  have := P.isAb.comm
  have h := isGrpPullback_pullback P.A (spMap (algebraMap (𝓞 K) K))
  obtain ⟨v, hv⟩ := TenDim.exists_isLieBasis _ (TorsionTauCompare.polOfPullback P _ h).smoothDim
  exact ⟨⟨TorsionTauCompare.polOfPullback P _ h, _, ⟨rfl, h, PolBaseChange.lbIso_refl (pull_isLB P.isLB _)⟩, v, hv⟩⟩

theorem dim_eq {ρ : 𝓞 K} {p q : ℕ} (T : PAT H (Sp (𝓞 K))) (hs : Splits E K) (ht : HasType H T.t.act ρ p q)
    (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) : T.g = Module.finrank ℚ E / 2 * (p + q) := by
  obtain ⟨F⟩ := nonempty_genFib T.pol
  exact (EigDec.eigen_decomposition E H K ρ T F p q hs ht hρ).2.2.2.1

variable {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

end Object

end GlobalTheory.CMSharedCompare
