module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer

noncomputable section

namespace GlobalTheory.EvalNat

theorem evalAt_natural : ∀ {X : Scheme.{0}} {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U), ∃ h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U, (∀ f : Γ(X, U), evalAt (spMap φ ≫ x) U h' f = φ (evalAt x U h f)) ∧ ∀ (U' : X.Opens) (i : U ≤ U') (h'' : ⊤ ≤ x ⁻¹ᵁ U') (f : Γ(X, U')), evalAt x U' h'' f = evalAt x U h ((X.presheaf.map (homOfLE i).op).hom f) := by
  intro X C C' _ _ φ x U h
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ ↦ h (Set.mem_univ ((spMap φ) p))
  refine ⟨h', fun f ↦ ?_, fun U' i h'' f ↦ ?_⟩
  · have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C')).hom =
        x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom ≫ CommRingCat.ofHom φ := by
      rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
      congr 2
    exact congrArg (fun t ↦ t.hom f) e
  · have e : x.appLE U' ⊤ h'' = X.presheaf.map (homOfLE i).op ≫ x.appLE U ⊤ h := by
      rw [Scheme.Hom.map_appLE]
    unfold evalAt
    rw [e]
    rfl

end GlobalTheory.EvalNat
