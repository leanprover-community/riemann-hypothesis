module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.UnitaryParam

theorem map_star_eq_map_inv_of_form : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ), (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) → (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) → (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) → ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w (π.locRep w) B → B.map star = B.map (·⁻¹) := by
  intro E _ _ _ a π H hH hpos hinv w B hB
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
  refine GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w a π.V (π.locRep w) x B ?_ hx
  refine ⟨H.flip, fun v u => ?_, fun v hv => ?_, fun g v u => ?_⟩
  · simp only [LinearMap.flip_apply]
    exact (hH u v).symm
  · simpa only [LinearMap.flip_apply] using hpos v hv
  · simp only [LinearMap.flip_apply]
    exact hinv _ u v

end GlobalTheory.CuspRep.UnitaryParam
