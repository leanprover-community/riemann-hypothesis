module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

namespace GlobalTheory.CechPoset

theorem pr_monotone {κ : Type} [LinearOrder κ] {X' X'' : Scheme.{0}} {ψ : X'' ⟶ X'} (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) :
    Monotone (pr D' hD' D'' hD'' hle) := fun _ _ h =>
  Subtype.mk_le_mk.2 (Prod.mk_le_mk.2 ⟨cov_mono D'' hD'' h, cov_mono D' hD' h⟩)

theorem restrict_pull1_pullHO1 {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}}
    {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'}
    (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i)
    (y : HO1 s') :
    (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull1 (pullHO1 w y) =
      (pullCoef w D' hD' D'' hD'' hle).pull1
        ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull1 y) := by
  have hp : (pairPull w).pull1 y = (pairRes ψ s'').pull1 (pullHO1 w y) := isPullO_pullHO1 w y
  generalize pullHO1 w y = z at hp
  let n := CoefMap.restrict (OPair ψ s'') (pr_monotone D' hD' D'' hD'' hle).functor.op
  have h1 : (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull1 z =
      n.pull1 ((pairRes ψ s'').pull1 z) := by
    refine Eq.trans ?_ ((pairRes ψ s'').pullCohomologyOne_comp n z)
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ ((pairRes ψ s'').comp n) { app U := 𝟙 _ }
      (fun U b ↦ mp_id (OAff s'') _ b) z
  rw [h1, ← hp]
  refine ((pairPull w).pullCohomologyOne_comp n y).symm.trans (Eq.trans ?_ (CoefMap.pullCohomologyOne_comp _ _ y))
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) y

end GlobalTheory.CechPoset
