module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.AdmQuotExt

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X]

def redExt (c : O) : ((↥L.T ⊗[O] X) × O) →ₗ[O] ((↥L.T ⊗[O] X) × (O ⧸ Ideal.span {c})) :=
  LinearMap.prodMap LinearMap.id (Ideal.span {c}).mkQ

omit [TopologicalSpace G] in
theorem redExt_surjective (c : O) : Function.Surjective (redExt L X c) := by
  rintro ⟨m, y⟩
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  exact ⟨(m, y), rfl⟩

omit [TopologicalSpace G] in
theorem ker_redExt (lam : O) (a : ℕ) : LinearMap.ker (redExt L X (lam ^ a)) = tableLineDegreeTwo.kerExt L X lam a := by
  rw [redExt, LinearMap.ker_prodMap, LinearMap.ker_id, Submodule.ker_mkQ]
  rfl

theorem redExt_actExt (χ₁ : G →* Oˣ) {c : O} (hc : ∀ x : X, c • x = 0)
    (z : G → ↥L.T ⊗[O] X) (hz : z ∈ Z1 (twCoef (latRep L) χ₁ X) ⊤) (g : G) (x : (↥L.T ⊗[O] X) × O) :
    redExt L X c (tableLineDegreeTwo.actExt L X χ₁ z g x) = Ea (latRep L) χ₁ hc ⟨z, hz⟩ g (redExt L X c x) := by
  obtain ⟨m, y⟩ := x
  have h := Ea_apply (latRep L) χ₁ hc ⟨z, hz⟩ g m y
  change (_, _) = Ea (latRep L) χ₁ hc ⟨z, hz⟩ g (m, Ideal.Quotient.mk _ y)
  rw [h]
  simp only [tableLineDegreeTwo.actExt, smul_smul, mul_comm y]
  rfl

end Gen


set_option maxHeartbeats 2000000 in
theorem admissible_quotientExtension_iff_admissible_ext' : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ),
    (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) →
    ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T.ρ) (X : Type) [AddCommGroup X] [Module S.O X]
      (z : S.G → ↥L.T ⊗[S.O] X) (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤) (a : ℕ)
      (ha : ∀ x : X, S.Γ.lam ^ a • x = 0),
      (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
                         (tableLineDegreeTwo.kerExt L X S.Γ.lam a) ↔ S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩)) := by
  intro l _ P S jT hj T L X _ _ z hz a ha
  have h := GlobalTheory.FullCharpoly.admissibleQuotient_iff_admissible_module S jT hj _ _ (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
    (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩) (redExt L X (S.Γ.lam ^ a)) (redExt_surjective L X _)
    (redExt_actExt L X S.Γ.χ₁ ha z hz)
  rw [ker_redExt L X S.Γ.lam a] at h
  exact h

end GlobalTheory.AdmQuotExt
