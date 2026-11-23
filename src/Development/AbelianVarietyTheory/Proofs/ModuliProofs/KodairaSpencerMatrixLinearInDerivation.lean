module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAnalyticKodairaSpencerClassStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FderivFnAddLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Lin

section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} {u : HolUnif A₀ L₀ g} {X : Scheme.{0}}
  {R : Type} [CommRing R] {p : X ⟶ Sp R} {m : A₀.left ⟶ X}

theorem ksRel_add {D D' : R → ℂ} {Θ Θ' : Matrix (Fin g) (Fin g) ℂ}
    {s s' : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ}
    (h : KSRel u p m D Θ s) (h' : KSRel u p m D' Θ' s') :
    KSRel u p m (fun r => D r + D' r) (Θ + Θ') (fun z W f => s z W f + s' z W f) := by
  refine { der := ?_, base := ?_, hol := ?_, per := ?_ }
  · intro z
    refine { add := ?_, mul := ?_, res := ?_ }
    · intro W hW f f'
      simp only [(h.der z).add W hW, (h'.der z).add W hW]
      ring
    · intro W hW f f'
      simp only [(h.der z).mul W hW, (h'.der z).mul W hW]
      ring
    · intro W W' hle hW' f
      simp only [(h.der z).res W W' hle hW', (h'.der z).res W W' hle hW']
  · intro z r
    simp only [h.base, h'.base]
  · intro W f
    exact (h.hol W f).add (h'.hol W f)
  · intro l W f z hz
    simp only [h.per l W f z hz, h'.per l W f z hz, Matrix.add_mulVec, map_add (f := _)]
    ring

theorem ksRel_smul (c : ℂ) {D : R → ℂ} {Θ : Matrix (Fin g) (Fin g) ℂ}
    {s : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ} (h : KSRel u p m D Θ s) :
    KSRel u p m (fun r => c * D r) (c • Θ) (fun z W f => c * s z W f) := by
  refine { der := ?_, base := ?_, hol := ?_, per := ?_ }
  · intro z
    refine { add := ?_, mul := ?_, res := ?_ }
    · intro W hW f f'
      simp only [(h.der z).add W hW]
      ring
    · intro W hW f f'
      simp only [(h.der z).mul W hW]
      ring
    · intro W W' hle hW' f
      simp only [(h.der z).res W W' hle hW']
  · intro z r
    simp only [h.base]
  · intro W f
    exact (h.hol W f).const_mul c
  · intro l W f z hz
    simp only [h.per l W f z hz, Matrix.smul_mulVec, map_smul, smul_eq_mul]
    ring
end

theorem ks_linear : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (o R : Type) [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap (algebraMap R ℂ)) → ∃ κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin P₀.g) (Fin P₀.g) ℂ, ∀ D : Derivation o R ℂ, ∃ s, KSRel u p m (fun r => D r) (κ D) s := by
  intro P₀ u Hm χ hG o R _ _ _ _ _ _ X p m hs hpb
  have hder : ∀ D : Derivation o R ℂ, IsDer (algebraMap R ℂ) (fun r => D r) := fun D =>
    ⟨fun a b => D.map_add a b, fun a b => by
      show D (a * b) = _
      rw [D.leibniz, Algebra.smul_def, Algebra.smul_def]⟩
  have hex : ∀ D : Derivation o R ℂ, ∃ Θ s, KSRel u p m (fun r => D r) Θ s := fun D =>
    GlobalTheory.T.exists_analytic_kodairaSpencer_class P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ (hder D)
  choose Θ s hΘ using hex
  have huniq : ∀ (D : Derivation o R ℂ) Θ' s', KSRel u p m (fun r => D r) Θ' s' → Θ D = Θ' :=
    fun D Θ' s' h => GlobalTheory.KS.Uniq.ks_unique P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ _ _ _ _ (hΘ D) h
  refine ⟨{ toFun := Θ, map_add' := ?_, map_smul' := ?_ }, fun D => ⟨s D, hΘ D⟩⟩
  · intro D D'
    apply huniq (D + D')
    have e : (fun r => (D + D') r) = fun r => D r + D' r := funext (add_apply D D')
    rw [e]
    exact ksRel_add (hΘ D) (hΘ D')
  · intro c D
    rw [RingHom.id_apply]
    apply huniq (c • D)
    have e : (fun r => (c • D) r) = fun r => c * D r := funext fun r => by
      rw [smul_apply, smul_eq_mul]
    rw [e]
    exact ksRel_smul c (hΘ D)

end GlobalTheory.KS.Lin
