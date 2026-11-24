module

public import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DetAlg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.JInjCore
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB

variable {K : Type} [Field K]
  (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
  (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
    (S →ₐ[K] T) → pts S → pts T → Prop)

theorem evalAt_eq_of (hWD : EvalWD pts mapR) (f : Rules pts) (hf : IsNatural pts mapR f)
    {S : Type} [CommRing S] [Algebra K S] (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R) (w : pts S)
    (h : mapR φ y w) : evalAt pts mapR f w = φ (f p y) := by
  have hT : FromTest pts mapR w := ⟨p, φ, y, h⟩
  unfold evalAt
  rw [dite_eq_left hT]
  exact hWD f hf S _ p _ φ _ y w hT.choose_spec.choose_spec.choose_spec h

theorem indep_of_complex [Algebra K ℂ] (hWD : EvalWD pts mapR)
    (hBC : ∀ (p : TRing K) (φ : p.R →ₐ[K] ℂ) (y : pts p.R), ∃ z : pts ℂ, mapR φ y z)
    {n : ℕ} (b : Fin n → Rules pts) (hnat : ∀ i, IsNatural pts mapR (b i)) (hb : LinearIndependent K b)
    (c : Fin n → ℂ) (hc : ∀ z : pts ℂ, FromTest pts mapR z → ∑ i, c i * evalAt pts mapR (b i) z = 0) :
    c = 0 := by
  classical
  haveI : CharZero K := (algebraMap K ℂ).charZero
  let F := AlgebraicClosure K
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  haveI : Normal K F := IsAlgClosure.normal K F
  haveI : Algebra.IsSeparable K F := IsAlgClosure.separable K F
  haveI : IsGalois K F := ⟨⟩
  let ι : F →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let Pt := Σ p : TRing K, pts p.R × (p.R →ₐ[K] F)
  let v : Rules pts →ₗ[K] (Pt → F) :=
    { toFun := fun f q => q.2.2 (f q.1 q.2.1)
      map_add' := by
        intro f g; funext q
        change q.2.2 (f q.1 q.2.1 + g q.1 q.2.1) = q.2.2 (f q.1 q.2.1) + q.2.2 (g q.1 q.2.1)
        exact map_add _ _ _
      map_smul' := by
        intro a f; funext q
        change q.2.2 (a • f q.1 q.2.1) = a • q.2.2 (f q.1 q.2.1)
        exact map_smul _ _ _ }
  let act : (F ≃ₐ[K] F) → Pt → Pt := fun g q => ⟨q.1, q.2.1, (g : F →ₐ[K] F).comp q.2.2⟩
  have hbij : ∀ g, Function.Bijective (act g) := by
    intro g
    refine Function.bijective_iff_has_inverse.mpr ⟨act g.symm, ?_, ?_⟩
    · rintro ⟨p, y, φ⟩
      exact Sigma.ext rfl (heq_of_eq (Prod.ext rfl (AlgHom.ext fun r => by simp [act])))
    · rintro ⟨p, y, φ⟩
      exact Sigma.ext rfl (heq_of_eq (Prod.ext rfl (AlgHom.ext fun r => by simp [act])))
  have heq : ∀ g f y, v f (act g y) = g (v f y) := fun _ _ _ => rfl
  have hinj : Function.Injective v := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf0
    funext p y
    apply detAlg_holds K p.n p.I p.3 (f p y)
    intro L _ _ _ φ
    let e : L →ₐ[K] F := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have h1 : e (φ (f p y)) = 0 := congrFun hf0 ⟨p, y, e.comp φ⟩
    exact e.toRingHom.injective (h1.trans (map_zero e).symm)
  have hli := indepDescent_holds K F ι.toRingHom (Rules pts) Pt v act hbij heq hinj n b hb
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  refine hli c ?_ i
  funext q
  obtain ⟨p, y, φ⟩ := q
  let ψ : p.R →ₐ[K] ℂ := ι.comp φ
  obtain ⟨z, hz⟩ := hBC p ψ y
  have h0 := hc z ⟨p, ψ, y, hz⟩
  simp only [evalAt_eq_of pts mapR hWD (b _) (hnat _) p ψ y z hz] at h0
  simpa [Finset.sum_apply, v, ψ] using h0

end ReciprocityTheory.ChartRestriction.G.PullbackSections
