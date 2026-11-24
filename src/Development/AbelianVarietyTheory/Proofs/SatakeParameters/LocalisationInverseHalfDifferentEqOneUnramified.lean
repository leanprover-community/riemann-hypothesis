module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.AlgebraMapFinite
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory.TwV.Xc

theorem not_dvd_absDifferent_of_not_mem_sq {E : Type} [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (P : HeightOneSpectrum (𝓞 E)) (h1 : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal)
    (h2 : ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) : ¬ P.asIdeal ∣ differentIdeal ℤ (𝓞 E) := by
  have hP : P.asIdeal.IsMaximal := P.isMaximal
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime _
  have : Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod p).toEquiv.symm
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) =
      Ideal.span {((p : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P.asIdeal := by
    rw [hmap, Ideal.span_singleton_le_iff_mem]
    exact h1
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hle
  have hcop : IsCoprime P.asIdeal Q := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have heq := hP.eq_of_le hne le_sup_left
    have hQP : Q ≤ P.asIdeal := heq ▸ le_sup_right
    apply h2
    have hmem : ((p : ℕ) : 𝓞 E) ∈
        Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) := by
      rw [hmap]; exact Ideal.subset_span rfl
    rw [hQ] at hmem
    rw [pow_two]
    exact Ideal.mul_mono_right hQP hmem
  exact not_dvd_differentIdeal_of_isCoprime ℤ P.asIdeal Q hcop hQ.symm

theorem inverseHalfDifferent_local_trivial_at_prime_norm : ∀ (D : D7) (p : ℕ), p.Prime → ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ((p : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  intro D p hp P h1 h2
  have hnd := not_dvd_absDifferent_of_not_mem_sq p hp P h1 h2
  have ht : differentIdeal ℤ (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) *
      (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) :=
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)
  have hspec : D.host.𝔟 ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) := ⟨_, D.host.𝔟_spec.1⟩
  have hn : ¬ D.host.𝔟 ≤ P.asIdeal := fun h => hnd (by
    rw [ht]
    exact ((Ideal.dvd_iff_le.2 h).trans hspec).mul_right _)
  obtain ⟨t, htb, htP⟩ := SetLike.not_le_iff_exists.1 hn
  have hb : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => hn (h ▸ bot_le)
  ext x
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨t * s, fun h => (P.isPrime.mem_or_mem h).elim htP hs, ?_⟩
    obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff hb).1 hx _ (FractionalIdeal.mem_coeIdeal_of_mem _ htb))
    rw [Submodule.mem_one]
    refine ⟨u, ?_⟩
    rw [hu, mul_smul, Algebra.smul_def t, mul_comm]
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    obtain ⟨u, hu⟩ := Submodule.mem_one.1 hx
    refine (FractionalIdeal.mem_inv_iff hb).2 fun y hy => ?_
    obtain ⟨z, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨u * z, by rw [map_mul, hu]⟩

end GlobalTheory.TwV.Xc
