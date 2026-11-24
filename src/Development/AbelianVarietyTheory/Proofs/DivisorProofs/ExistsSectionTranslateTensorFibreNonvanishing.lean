module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistNonvanishingRationalPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingTwistedSectionsDescendFieldExtensionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistFibreGen

theorem exists_sec_of_closed {X : Scheme.{0}} [CompactSpace X] (M : LB X)
    (h : ∀ z : X, IsClosed ({z} : Set X) → ∃ s : LB.Sec M, z ∈ nonzeroLocus s) (z : X) :
    ∃ s : LB.Sec M, z ∈ nonzeroLocus s := by
  by_contra hz
  push_neg at hz
  let C : Set X := ⋂ s : LB.Sec M, ((nonzeroLocus s : X.Opens) : Set X)ᶜ
  have hC : IsClosed C := isClosed_iInter fun s => (nonzeroLocus s).isOpen.isClosed_compl
  obtain ⟨w, hw, hcl⟩ := hC.exists_closed_singleton ⟨z, Set.mem_iInter.2 fun s => hz s⟩
  obtain ⟨s, hs⟩ := h w hcl
  exact Set.mem_iInter.1 hw s hs

theorem compactSpace_fibre {S : Scheme.{0}} (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) : CompactSpace (Over.mk t ⊗ P.A).left := by
  have := P.isAb.proper
  have : QuasiCompact (pullback.fst t P.A.hom) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst t P.A.hom)

theorem exists_sec_algClosed {S : Scheme.{0}} (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (z : (Over.mk t ⊗ P.A).left) :
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), z ∈ nonzeroLocus s := by
  have := compactSpace_fibre P K t
  refine exists_sec_of_closed _ (fun z hz => ?_) z
  have := P.isAb.smooth
  have : LocallyOfFiniteType (fst (Over.mk t) P.A).left :=
    (inferInstance : LocallyOfFiniteType (pullback.fst t P.A.hom))
  let f := (fst (Over.mk t) P.A).left
  let p₀ := pointOfClosedPoint f z hz
  have hw : p₀ ≫ (Over.mk t ⊗ P.A).hom = (Over.mk t).hom := by
    rw [← Over.w (fst (Over.mk t) P.A), ← Category.assoc, pointOfClosedPoint_comp]
    exact Category.id_comp _
  let q : Over.mk t ⟶ Over.mk t ⊗ P.A := Over.homMk p₀ hw
  have hq : q ≫ fst (Over.mk t) P.A = 𝟙 _ := by
    ext1
    exact pointOfClosedPoint_comp f z hz
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_twist_nonvanishing_rationalPoint S P K t c (q ≫ snd _ _) (IsLocalRing.closedPoint _)
  refine ⟨s, ?_⟩
  have e : lift (𝟙 (Over.mk t)) (q ≫ snd (Over.mk t) P.A) = q := by
    rw [← hq, lift_comp_fst_snd]
  rw [e] at hs
  have h2 : q.left (IsLocalRing.closedPoint K) = z := pointOfClosedPoint_apply f z hz _
  rw [← h2]
  exact hs

theorem exists_sec_mem_nonzeroLocus : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left),
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  intro S P k _ t c y
  exact GlobalTheory.T.nonvanishing_twistedSections_descend_fieldExtension S P k (AlgebraicClosure k) t c (fun z => exists_sec_algClosed P _ _ _ z) y

end GlobalTheory.TwistFibreGen
