module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory

theorem trEll_latticeConj_move : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n n' : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E) (L : Submodule (𝓞 E) (Fin n → E)) (L' : Submodule (𝓞 E) (Fin n' → E)) (v : HeightOneSpectrum (𝓞 F)) (j : GLoc σ J v ≃ₜ* GLoc σ J' v), IsLatticeConj L L' j → XSet P (Fv F v) J' = XSet P (Fv F v) J ∧ ∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin n → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), ∃ (φ' : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)) (h' : IsIsom P (Fv F v) J' x.1.1 φ'), gam h' = j (gam h) ∧ ∀ t, torEmb h' t = j (torEmb h t) := by
  intro F E _ _ _ _ _ σ _ r n n' P J J' L L' v j hj
  obtain ⟨a, ha, -, hja⟩ := hj
  have iso : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)),
      IsIsom P (Fv F v) J x φ → IsIsom P (Fv F v) J' x (φ.trans a) := by
    intro x φ h y y'
    have e := ha (φ y) (φ y')
    simp only [GlobalTheory.AdelicU.hLin, hR] at e
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e]
    exact h y y'
  have iso' : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)),
      IsIsom P (Fv F v) J' x φ → IsIsom P (Fv F v) J x (φ.trans a.symm) := by
    intro x φ h y y'
    have e := ha (a.symm (φ y)) (a.symm (φ y'))
    simp only [GlobalTheory.AdelicU.hLin, hR, LinearEquiv.apply_symm_apply] at e
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← e]
    exact h y y'
  have tor : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
      (h : IsIsom P (Fv F v) J x φ) (t : Tor P (Fv F v)), torEmb (iso x φ h) t = j (torEmb h t) := by
    intro x φ h t
    apply GlobalTheory.AdelicU.matHom_injective (Fv F v) σ J'
    apply Units.ext
    have key : ∀ w, (GlobalTheory.AdelicU.matHom _ σ J' (torEmb (iso x φ h) t)).1 *ᵥ w =
        (GlobalTheory.AdelicU.matHom _ σ J' (j (torEmb h t))).1 *ᵥ w := by
      intro w
      obtain ⟨y, rfl⟩ := (φ.trans a).surjective w
      rw [LinearEquiv.trans_apply, hja]
      change mulMat (φ.trans a) (torUnit t).1 *ᵥ (φ.trans a) y = a (mulMat φ (torUnit t).1 *ᵥ φ y)
      rw [mulMat_mulVec, mulMat_mulVec]
      rfl
    exact Matrix.ext_of_mulVec_single fun i => key _
  refine ⟨?_, fun x φ h => ⟨φ.trans a, iso _ φ h, tor _ φ h _, tor _ φ h⟩⟩
  ext q
  constructor
  · rintro ⟨x, φ, e, h⟩
    exact ⟨x, φ.trans a.symm, e, iso' _ φ h⟩
  · rintro ⟨x, φ, e, h⟩
    exact ⟨x, φ.trans a, e, iso _ φ h⟩

end GlobalTheory
