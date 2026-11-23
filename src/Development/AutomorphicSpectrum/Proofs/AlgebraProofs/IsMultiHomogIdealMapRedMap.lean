module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

abbrev redMap (ι : K → Type*) (p : ℕ) : MRing ι →+* MRingOver (ZMod p) ι :=
  MvPolynomial.map (Int.castRingHom (ZMod p))

theorem redMap_surjective (p : ℕ) : Function.Surjective (redMap ι p) := by
  exact MvPolynomial.map_surjective _ ZMod.intCast_surjective

theorem natCast_charOf_mem (W : Ideal (MRing ι)) : ((charOf W : ℕ) : MRing ι) ∈ W := by
  have hc : charOf W = (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs := rfl
  rw [hc]
  set g := Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) with hgdef
  have hg : C g ∈ W := Ideal.mem_comap.mp (Submodule.IsPrincipal.generator_mem _)
  have h : C (g.natAbs : ℤ) ∈ W := by
    rcases Int.natAbs_eq g with h | h
    · rw [← h]; exact hg
    · have e : (g.natAbs : ℤ) = -g := by linarith
      rw [e, map_neg]; exact W.neg_mem hg
  rw [← map_natCast (C : ℤ →+* MRing ι) g.natAbs]
  exact h

theorem ker_redMap_le {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    RingHom.ker (redMap ι p) ≤ W := by
  rw [redMap, MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
    Ideal.span_le, Set.singleton_subset_iff]
  simpa using hp

theorem comap_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    (W.map (redMap ι p)).comap (redMap ι p) = W := by
  rw [Ideal.comap_map_of_surjective _ (redMap_surjective p), ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr (ker_redMap_le hp)]

theorem isMultiHomog_redMap {p : ℕ} {s : MRing ι} {a : K → ℕ} (h : IsMultiHomog s a) :
    IsMultiHomog (redMap ι p s) a := by
  intro m hm k
  refine h m ?_ k
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  intro h0
  apply hm
  simp [redMap, MvPolynomial.coeff_map, h0]

theorem isMultiHomogIdeal_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (h : IsMultiHomogIdeal W) :
    IsMultiHomogIdeal (W.map (redMap ι p)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine ⟨redMap ι p '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, isMultiHomog_redMap ha⟩

theorem isRelevant_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W)
    (h : IsRelevant W) : IsRelevant (W.map (redMap ι p)) := by
  intro k
  obtain ⟨i, hi⟩ := h k
  refine ⟨i, fun hx => hi ?_⟩
  rw [← comap_map_redMap hp, Ideal.mem_comap]
  simpa [redMap] using hx

def quotRedEquiv {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    (MRing ι ⧸ W) ≃+* (MRingOver (ZMod p) ι ⧸ W.map (redMap ι p)) :=
  (Ideal.quotEquivOfEq (by
      rw [← RingHom.comap_ker, Ideal.mk_ker, comap_map_redMap hp])).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk (W.map (redMap ι p))).comp (redMap ι p))
      (Ideal.Quotient.mk_surjective.comp (redMap_surjective p)))

theorem isProjVarF_map_redMap {p : ℕ} [Fact p.Prime] {W : Ideal (MRing ι)} {n : ℕ}
    (hp : ((p : ℕ) : MRing ι) ∈ W) (hW : IsMultiProjPrime W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (W.map (redMap ι p)) n := by
  obtain ⟨hWp, hWh, hWr⟩ := hW
  refine ⟨⟨?_, isMultiHomogIdeal_map_redMap hWh, isRelevant_map_redMap hp hWr⟩, ?_⟩
  · exact Ideal.map_isPrime_of_surjective (redMap_surjective p) (ker_redMap_le hp)
  · rw [← ringKrullDim_eq_of_ringEquiv (quotRedEquiv hp)]
    exact hdim

theorem fibreComp : ReciprocityTheory.ChartRestriction.G.AI.I2.FibreCompStatement := by
  intro K _ ι _ P n A s W hP hs hW hv
  obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  obtain ⟨a, -, hsa, hsP⟩ := hs
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have hWmh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hsa hWmin
  have hmp : IsMultiProjPrime W := ⟨hWp, hWmh, hWrel⟩
  have hp := charOf_prime hWp hv
  have := hPp
  have h1 := dim_quot_minimal_add_one P W s hsP hWmin
  rw [hPdim] at h1
  have hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    withBot_eq_of_add_one (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])
  refine ⟨hp, natCast_charOf_mem W, hmp, ?_⟩
  haveI : Fact (charOf W).Prime := ⟨hp⟩
  exact isProjVarF_map_redMap (natCast_charOf_mem W) hmp hdim

end GlobalTheory.CompanionTheory.Ar.Pub
