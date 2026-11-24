module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostCompletionLeMaxUnramifiedPadic
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.HubLoc

open Formalism.FrobeniusOrbits

section Gen

variable {l : ℕ} [Fact l.Prime] {R : Ranks} (H : Host R) (J : H.E →+* Om l)

theorem kw_eq_sup_of_gens (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) (g₁ g₂ g₃ : H.E)
    (hgen : ∀ M : IntermediateField ℚ_[l] (Om l), J g₁ ∈ M → J g₂ ∈ M → J g₃ ∈ M → ∀ x : H.E, J x ∈ M) :
    Kw.1 = IntermediateField.adjoin ℚ_[l] ({J g₁, J g₂} : Set (Om l)) ⊔
      IntermediateField.adjoin ℚ_[l] {J g₃} := by
  set M := IntermediateField.adjoin ℚ_[l] ({J g₁, J g₂} : Set (Om l)) with hM
  set N := M ⊔ IntermediateField.adjoin ℚ_[l] {J g₃} with hN
  have hfM : FiniteDimensional ℚ_[l] ↥M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral (R := ℚ_[l]) x
  have hfy : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {J g₃}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) _)
  have hfN : FiniteDimensional ℚ_[l] ↥N := IntermediateField.finiteDimensional_sup _ _
  have hcl : IsClosed ((N : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional N.toSubalgebra.toSubmodule
  have h1 : J g₁ ∈ N := le_sup_left (a := M) (IntermediateField.subset_adjoin _ _ (by simp))
  have h2 : J g₂ ∈ N := le_sup_left (a := M) (IntermediateField.subset_adjoin _ _ (by simp))
  have h3 : J g₃ ∈ N := le_sup_right (a := M) (IntermediateField.mem_adjoin_simple_self _ _)
  apply le_antisymm
  · intro x hx
    refine closure_minimal ?_ hcl (hdense hx)
    rintro _ ⟨z, rfl⟩
    exact hgen N h1 h2 h3 z
  · refine sup_le ?_ ?_
    · rw [hM, IntermediateField.adjoin_le_iff]
      rintro _ (rfl | rfl)
      exacts [hE g₁, hE g₂]
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact hE g₃

theorem sq_aE_image : (J (H.sqq)) ^ 2 = -(H.q : Om l) := by
  rw [← map_pow, H.sqq_sq]; simp

theorem sq_bE_image : (J (H.sqd)) ^ 2 = -(H.d : Om l) := by
  rw [← map_pow, H.sqd_sq]; simp

theorem kw_eq_sup_sqrt (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) (hl : l = H.q ∨ l = H.d) :
    ∃ M : IntermediateField ℚ_[l] (Om l), M ≤ MaximalUnramifiedExtension l ∧ ∃ y : Om l, y ^ 2 = -(l : Om l) ∧
      Kw.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} := by
  have hh := H.hyp
  have hq2 : H.q % 4 = 3 := by have := hh.2.2.1; omega
  have hd2 : H.d % 4 = 3 := by have := hh.2.2.2.1; omega
  have hqd : H.q ≠ H.d := by have := hh.2.2.1; have := hh.2.2.2.1; omega
  have hlS : ¬ l ∣ H.QS := UpperTheory.Small.not_dvd_QS H Fact.out (UpperTheory.Small.not_mem_of_qd H hl)
  have hθ := theta_mem_Kur H J
  rcases hl with rfl | rfl
  · refine ⟨_, ?_, _, sq_aE_image H J, kw_eq_sup_of_gens H J Kw hE hdense (thL H H.q) (H.sqd)
      (H.sqq) fun M m1 m2 m3 x => image_le H J hlS M m1 m3 m2 x⟩
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · exact hθ
    · exact sqrtKur_holds _ H.d hh.2.1 hd2 hqd.symm _ (sq_bE_image H J)
  · refine ⟨_, ?_, _, sq_bE_image H J, kw_eq_sup_of_gens H J Kw hE hdense (thL H H.d) (H.sqq)
      (H.sqd) fun M m1 m2 m3 x => image_le H J hlS M m1 m2 m3 x⟩
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · exact hθ
    · exact sqrtKur_holds _ H.q hh.1 hq2 hqd _ (sq_aE_image H J)

end Gen

theorem kw_eq_unram_sup_sqrt : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    ∃ M : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)), M ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
      ∃ y : Om (D.nd.l i), y ^ 2 = -(D.nd.l i : Om (D.nd.l i)) ∧
        (D.nbr i w hw).Kw.1 = M ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y} := by
  intro D i hl w hw
  exact kw_eq_sup_sqrt D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) (D.nbr i w hw).Kw
    (D.nbr i w hw).j_E (D.nbr i w hw).j_dense hl

end GlobalTheory.HubLoc
