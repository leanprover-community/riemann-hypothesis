module

public import Formalism.LocalToGlobal.ProjectiveLattices.VAddIntNonneg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp


noncomputable section

namespace GlobalTheory.FlatUnit
open GlobalTheory.FlatLine

theorem val_sum_nonneg {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    {la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : Formalism.L2.Pj.IsVal la v) {ι : Type}
    (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, 0 ≤ v (f i)) : 0 ≤ v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hv.zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) (hv.add _ _)

theorem val_nsmul_nonneg {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    {la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : Formalism.L2.Pj.IsVal la v) (n : ℕ) {f : R}
    (h : 0 ≤ v f) : 0 ≤ v (n • f) := by
  have := val_sum_nonneg hv (Finset.range n) (fun _ => f) (fun _ _ => h)
  simpa [Finset.sum_const, Finset.card_range] using this

theorem pnorm_sum_le {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {ι : Type} (s : Finset ι) (P : ι → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ)
    (y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : X.pnorm la (∑ i ∈ s, P i) y ≤ ∑ i ∈ s, X.pnorm la (P i) y := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
    Real.rpow_nonneg (norm_nonneg _) _)
  rw [Finset.sum_apply]
  exact norm_sum_le _ _

end GlobalTheory.FlatUnit

end
