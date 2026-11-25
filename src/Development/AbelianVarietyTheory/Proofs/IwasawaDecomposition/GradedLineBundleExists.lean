module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.Points

namespace GlobalTheory.GradedPieces

attribute [local instance] Over.cartesianMonoidalCategory

section Linear

variable {k M : Type} [Field k] [AddCommGroup M] [Module k M] {m : ℕ}

def Diag (p q : Fin m → M) (d : Fin m → k) : Prop :=
  ∀ a, ∃ cf : Fin m → k, cf a = d a ∧ (∀ b, a < b → cf b = 0) ∧ q a = ∑ b, cf b • p b

end Linear

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {m : ℕ}

theorem comb_map (φ : S →+* T) {x' : Sp T ⟶ X} (hx : spMap φ ≫ x = x')
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t x' (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  subst hx
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap T (DualNumber T)) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, Formalism.L2.Pj.dualMap_comp_alg])
  have e : ∀ a : S, spMap (dualMap φ) ≫ spMap (epsMul a) = spMap (epsMul (φ a)) ≫ spMap (dualMap φ) := fun a => by
    rw [spMap_comp_spMap, spMap_comp_spMap]
    congr 1
    refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, e, Category.assoc]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem basis_iff {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x Φ) {u : Fin m → (epsR S ⟶ G')} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hv : ∀ i, IsTanAtG t x (v i)) (e : ∀ i, pushHom h (epsR S) (u i) = tv (tanOf (hv i))) :
    IsLieBasis u ↔ ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x v cf w := by
  have key : ∀ a p (n : TanM x t.G), pushHom h (epsR S) p = tv n →
      (IsLieComb a u p ↔ IsCombAtG t x v a (tv n).left) := fun a p n hp => by
    rw [isLieComb_iff h, hp]
    simp only [e]
    refine Iff.trans ?_ (isCombAtG_iff t x (fun i => tv (tanOf (hv i))) a _).symm
    exact ⟨fun q => by rw [q], fun q => Over.OverMorphism.ext q.symm⟩
  refine ⟨fun hu w hw => ?_, fun hb => ⟨fun i => (isTangent_iff h _).2 (by rw [e]; exact tv_mem _), fun p hp => ?_⟩⟩
  · obtain ⟨p, hp⟩ := push_surj h (tv (tanOf hw))
    simpa only [key _ p _ hp, left_tanOf] using hu.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem _))
  · simpa only [key _ p (mkT _ ((isTangent_iff h p).1 hp)) rfl] using
      hb _ (isTan_tv (mkT _ ((isTangent_iff h p).1 hp)))

theorem basis_map (ψ : S →+* T) {x' : Sp T ⟶ X} (hx : spMap ψ ≫ x = x') {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hv : ∀ i, IsTanAtG t x (v i)) (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x v cf w) :
    ∀ w, IsTanAtG t x' w → ∃! cf, IsCombAtG t x' (fun i => spMap (dualMap ψ) ≫ v i) cf w := by
  subst hx
  have h₀ := isGrpPullback_pullback t.G x
  have h := isGrpPullback_pullback t.G (spMap ψ ≫ x)
  have hv' := fun i => isTan_map ψ rfl (hv i)
  choose u hu using fun i => push_surj h₀ (tv (tanOf (hv i)))
  choose u' hu' using fun i => push_surj h (tv (tanOf (hv' i)))
  have := t.semi.smooth
  have : Smooth ((Over.pullback x).obj t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  refine (basis_iff h hv' hu').1 (Chart.frameLieBCR _ ((basis_iff h₀ hv hu).2 hb) ψ
    (Chart.isGrpPullback_factor x (spMap ψ) h)
    (fun a b v hv => push_inj h (by
      have := smT_add _ _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => ?_)
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc]
    exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (hu i)).symm)
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (u i)).symm)
    exact (spMap_comp_spMap _ _).trans ((congrArg spMap (Formalism.L2.Pj.dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)

theorem dual_comp {R : Type} [CommRing R] (ρ : R →+* S) (ψ : S →+* T) {Y : Scheme.{0}} (v : Sp (DualNumber R) ⟶ Y) :
    spMap (dualMap ψ) ≫ spMap (dualMap ρ) ≫ v = spMap (dualMap (ψ.comp ρ)) ≫ v := by
  rw [← Category.assoc, spMap_comp_spMap]
  congr 2
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap]

variable {k : Type} [Field k] {y : Sp k ⟶ X}

variable (t y) in
def DiagAt (p q : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) (d : Fin m → k) : Prop :=
  ∀ a, ∃ cf : Fin m → k, cf a = d a ∧ (∀ b, a < b → cf b = 0) ∧ IsCombAtG t y p cf (q a)

end Tangent

end GlobalTheory.GradedPieces
