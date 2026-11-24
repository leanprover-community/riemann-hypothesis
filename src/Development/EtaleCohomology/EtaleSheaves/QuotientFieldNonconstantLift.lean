module

public import Development.EtaleCohomology.EtaleSheaves.LeafReducedSmooth
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.QuotientFieldNonconstantLift

def LeafCurveSmall : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  (Set.univ : Set C).Infinite ∧ ∀ Z : Set C, IsClosed Z → Z.Infinite → Z = Set.univ

def LeafLiftNonconst : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    ∀ (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))), genericPoint X ∈ Set.range e →
    ∀ y : C0, ∃ a : C0, pullback.lift c0 e he.symm a ≠ pullback.lift c0 e he.symm y

theorem lqf_of_nonconst (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C Y : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hc : IsCurve c) (g : C ⟶ Y) [LocallyOfFiniteType g] [UniversallyClosed g]
    (hn : ∀ y, ∃ a, g a ≠ g y) : LocallyQuasiFinite g := by
  obtain ⟨_, _, _⟩ := id hc
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  refine GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints g fun y hy => ?_
  have hcl : IsClosed ({g y} : Set Y) := by
    have := g.isClosedMap _ hy
    simpa using this
  by_contra hinf
  have := (hC Ω c hc).2 _ (hcl.preimage g.continuous) hinf
  obtain ⟨a, ha⟩ := hn y
  have : a ∈ g ⁻¹' {g y} := this ▸ Set.mem_univ a
  exact ha this

theorem nonconst_of_surj (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C0 C1 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (hc : IsCurve c0) (g : C1 ⟶ C0) (hg : Surjective g) (y : C1) : ∃ a, g a ≠ g y := by
  obtain ⟨b, hb⟩ := ((hC Ω c0 hc).1.sdiff (Set.finite_singleton (g y))).nonempty
  obtain ⟨a, rfl⟩ := hg.surj b
  exact ⟨a, by simpa using hb.2⟩

theorem lqf_gamma (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C0 C1 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (hc : IsCurve c0) (g : C1 ⟶ C0) (hc1 : IsCurve (g ≫ c0)) (hg : Surjective g) :
    LocallyQuasiFinite g := by
  obtain ⟨_, _, _⟩ := id hc
  obtain ⟨_, _, _⟩ := id hc1
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g c0
  have : UniversallyClosed g := UniversallyClosed.of_comp_of_isSeparated g c0
  exact lqf_of_nonconst hC (g ≫ c0) hc1 g (nonconst_of_surj hC c0 hc g hg)

theorem LeafQFOmega_of (hC : LeafCurveSmall) (hL : LeafLiftNonconst) :
    LateralTheory.E.QuasiFiniteDescent.LeafQFOmega := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  refine ⟨?_, lqf_gamma hC c0 hc0 γ1 h1 s1, lqf_gamma hC (γ1 ≫ c0) h1 γ2 h2 s2⟩
  obtain ⟨_, _, _⟩ := id hc0
  set g := pullback.lift c0 e he.symm with hgdef
  have hfst : g ≫ pullback.fst _ _ = c0 := pullback.lift_fst _ _ _
  have : LocallyOfFiniteType (g ≫ pullback.fst _ _) := by rw [hfst]; infer_instance
  have : UniversallyClosed (g ≫ pullback.fst _ _) := by rw [hfst]; infer_instance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (pullback.fst _ _)
  have : UniversallyClosed g := UniversallyClosed.of_comp_of_isSeparated g (pullback.fst _ _)
  exact lqf_of_nonconst hC c0 hc0 g (hL k p Ω hdim c0 e hc0 he hgen)

end LateralTheory.E.QuotientFieldNonconstantLift
