module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.etaleCohomology_simplicialCochain_representation_step {R : Type} [CommRing R] (a I : Ideal R) :
    IsConnected (PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R)) ↔
    IsConnected ((PrimeSpectrum.zeroLocus
      ((I.map (Ideal.Quotient.mk a) : Ideal (R ⧸ a)) : Set (R ⧸ a)))ᶜ :
        Set (PrimeSpectrum (R ⧸ a))) := by
  have hs : Function.Surjective (Ideal.Quotient.mk a) := Ideal.Quotient.mk_surjective
  have hemb := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (R ⧸ a) (Ideal.Quotient.mk a) hs
  have hr := range_comap_of_surjective (R ⧸ a) (Ideal.Quotient.mk a) hs
  rw [Ideal.mk_ker] at hr
  have hpre : (PrimeSpectrum.zeroLocus
      ((I.map (Ideal.Quotient.mk a) : Ideal (R ⧸ a)) : Set (R ⧸ a))) =
      PrimeSpectrum.comap (Ideal.Quotient.mk a) ⁻¹' PrimeSpectrum.zeroLocus (I : Set R) := by
    ext p
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_preimage, SetLike.coe_subset_coe,
      PrimeSpectrum.comap_asIdeal]
    exact Ideal.map_le_iff_le_comap
  have him : PrimeSpectrum.comap (Ideal.Quotient.mk a) '' ((PrimeSpectrum.zeroLocus
      ((I.map (Ideal.Quotient.mk a) : Ideal (R ⧸ a)) : Set (R ⧸ a)))ᶜ) =
      PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [hpre, ← Set.preimage_compl, Set.image_preimage_eq_inter_range, hr, Set.diff_eq,
      Set.inter_comm]
  rw [← him]
  unfold IsConnected
  rw [Set.image_nonempty, hemb.isInducing.isPreconnected_image]

theorem UpperTheory.V.AlgebraTools.Conn.bridge :
    ∀ {R : Type} [CommRing R] (a : Ideal R) (k : WithBot ℕ∞), ConnOn a k ↔ ReciprocityTheory.CA.ConnInDim (R ⧸ a) k := by
  intro R _ a k
  constructor
  · intro h J hJ
    have hs : Function.Surjective (Ideal.Quotient.mk a) := Ideal.Quotient.mk_surjective
    have hle : a ≤ J.comap (Ideal.Quotient.mk a) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact J.zero_mem
    have hJ' : (J.comap (Ideal.Quotient.mk a)).map (Ideal.Quotient.mk a) = J :=
      Ideal.map_comap_of_surjective _ hs J
    rw [← hJ'] at hJ ⊢
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hJ
    exact (etaleCohomology_simplicialCochain_representation_step a _).mp (h _ hle hJ)
  · intro h I hle hI
    rw [← ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hI
    exact (etaleCohomology_simplicialCochain_representation_step a I).mpr (h _ hI)
