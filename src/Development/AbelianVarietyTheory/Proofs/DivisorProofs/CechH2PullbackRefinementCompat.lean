module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

namespace GlobalTheory.CechPoset

theorem restrict_pull2_pullHO2 {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}}
    {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'}
    (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i))
    (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) (y : HO2 s') :
    (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull2 (pullHO2 w y) =
      (pullCoef w D' hD' D'' hD'' hle).pull2
        ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull2 y) := by
  have hm : Monotone (pr D' hD' D'' hD'' hle) := fun I J h =>
    Subtype.mk_le_mk.2 (Prod.mk_le_mk.2 ⟨cov_mono D'' hD'' h, cov_mono D' hD' h⟩)
  have h1 : (pairRes ψ s'').pull2 (pullHO2 w y) = (pairPull w).pull2 y :=
    (LinearEquiv.ofBijective (pairRes ψ s'').pull2 (pairRes_pull2_bijective ψ s'')).apply_symm_apply _
  have h2 := congrArg (CoefMap.restrict (OPair ψ s'') hm.functor.op).pull2 h1
  generalize pullHO2 w y = z at h2 ⊢
  obtain ⟨z, rfl⟩ := CatCoh.H2.mk_surjective _ z
  obtain ⟨y, rfl⟩ := CatCoh.H2.mk_surjective _ y
  exact h2

end GlobalTheory.CechPoset
