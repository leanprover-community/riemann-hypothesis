module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualInclUnit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Eb.locL_cyc (l : ℕ) [Fact l.Prime] :
    Continuous (Loc.cycA l l (PadicAlgCl l)) := by
  have hc : Continuous (Loc.cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (PadicAlgCl l)
  have ha : Continuous (algebraMap ℤ_[l] (PadicAlgCl l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map (algebraMap ℤ_[l] (PadicAlgCl l) : ℤ_[l] →* PadicAlgCl l) ha).comp hc

private theorem UpperTheory.V.Ws.Eb.locL_open {H K ι : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [TotallyDisconnectedSpace H] [Field K] [TopologicalSpace K] [T1Space K] [Finite ι]
    (f : ι → H → K) (hf : ∀ i, Continuous (f i)) (h1 : ∀ i, f i 1 = 1) {k : ℕ} (hk : 0 < k) :
    ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ i, ∀ g ∈ U, f i g ^ k = 1 → f i g = 1 := by
  have hfin : ({z : K | z ^ k = 1} \ {1}).Finite := by
    refine Set.Finite.subset (Multiset.finite_toSet (nthRoots k (1 : K))) fun z hz => ?_
    exact (mem_nthRoots hk).2 hz.1
  have ho : IsOpen (⋂ i, f i ⁻¹' ({z : K | z ^ k = 1} \ {1})ᶜ) :=
    isOpen_iInter_of_finite fun i => hfin.isClosed.isOpen_compl.preimage (hf i)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
    (Set.mem_iInter.2 fun i h => h.2 (h1 i))
  refine ⟨U.toOpenSubgroup.toSubgroup, U.toOpenSubgroup.isOpen, fun i g hg e => ?_⟩
  by_contra hne
  exact Set.mem_iInter.1 (hU hg) i ⟨e, hne⟩

theorem UpperTheory.V.Ws.Eb.locL :
    Loc.LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] (φ : H →* Formalism.BasicNotions.Loc.GQ l), Topology.IsOpenEmbedding φ →
        ∀ {n : ℕ} (ρ : H →* GL (Fin n) (PadicAlgCl l)), Continuous ρ → ∀ y ∈ Z1 (Loc.adGL ρ), ∀ ρ' : H →* GL (Fin n) (DualNumber (PadicAlgCl l)), IsTan ρ y ρ' → ∀ (κ : Fin n → H →* (DualNumber (PadicAlgCl l))ˣ) (m : Fin n → ℤ) (k : ℕ), W.HasFlag ρ' κ → (∀ i j, i < j → m j + 2 ≤ m i) → 0 < k →
        (∀ i g, φ g ∈ Loc.Iq l → (κ i g : DualNumber (PadicAlgCl l)).snd = 0 ∧ (W.pushCh (dF _) (κ i) g * Loc.cycA l l (PadicAlgCl l) (φ g) ^ (-m i)) ^ k = 1) → y ∈ Loc.finiteCocycles φ (Loc.adGL ρ) := by
  intro P l _ H _ _ _ _ _ φ hφ n ρ hρ y hy ρ' ht κ m k hF hm hk hκ
  have hpush : ∀ g, GeneralLinearGroup.map (dF (PadicAlgCl l)) (ρ' g) = ρ g := fun g =>
    Units.ext (Matrix.ext fun a b => congrArg TrivSqZeroExt.fst (ht g a b))
  have hκc : ∀ i, Continuous fun g => (κ i g : DualNumber (PadicAlgCl l)).fst := by
    obtain ⟨h, hh⟩ := hF
    intro i
    have e : (fun g => (κ i g : DualNumber (PadicAlgCl l)).fst) = fun g =>
        ((GeneralLinearGroup.map (dF (PadicAlgCl l)) h * ρ g * (GeneralLinearGroup.map (dF (PadicAlgCl l)) h)⁻¹ :
          GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i i := by
      funext g
      rw [← hpush, ← map_inv, ← map_mul, ← map_mul, ← (hh g).2 i]
      rfl
    rw [e]
    exact (Units.continuous_val.comp ((continuous_const.mul hρ).mul continuous_const)).matrix_elem i i
  obtain ⟨U, hUo, hU⟩ := locL_open
    (fun i g => ((W.pushCh (dF _) (κ i) g * Loc.cycA l l (PadicAlgCl l) (φ g) ^ (-m i) : (PadicAlgCl l)ˣ) : PadicAlgCl l))
    (fun i => (hκc i).mul (Units.continuous_val.comp (((locL_cyc l).comp hφ.continuous).zpow (-m i))))
    (fun i => by simp only [map_one, _root_.one_zpow, mul_one, Units.val_one]) hk
  refine Loc.pr6Bar P φ hφ ρ hρ y hy ρ' ht κ m hF (fun i j hij => by have := hm i j hij; omega) U hUo
    (fun i g hg hI => ?_) (fun i j hij => Or.inl (hm i j hij))
  obtain ⟨h0, h1⟩ := hκ i g hI
  have h2 := hU i g hg (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
  rw [Units.val_eq_one, _root_.zpow_neg, mul_inv_eq_one] at h2
  rw [← h2]
  exact TrivSqZeroExt.ext rfl h0
