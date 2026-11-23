module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneIsUnitOneSubPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardTorsionTrivialOfTorsorsHaveSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivial
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem pic_localization_strictHenselisation_no_torsion : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ c : CommRing.Pic (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), c ^ q = 1 → c = 1 := by
  intro T O _ _ _ _ _ _ _ _ _ q hT hq hq0 hSi c hc
  obtain ⟨P, hP, φ, hφ, hsh⟩ := GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T O hSi
  haveI : IsLocalRing O := hsh.1.toIsLocalRing
  obtain ⟨ζ, hζ, hζu⟩ := GlobalTheory.exists_pow_eq_one_isUnit_one_sub_pow T q hq0 hq hT.2
  refine GlobalTheory.T.picard_torsion_trivial_of_torsors_have_sections _ q hq0 ?_ ⟨algebraMap T _ ζ, ?_, ?_⟩ ?_ c hc
  · simpa using hq.map (algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  · rw [← map_pow, hζ, map_one]
  · intro k hk hkq
    simpa using (hζu k hk hkq).map (algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  · intro D _ _ h1 h2 h3 act hact
    exact GlobalTheory.LocAcyc.torsor_trivial T O hT.2 P φ hφ hsh q hq0 hq D h1 h2 h3 act hact

end GlobalTheory
