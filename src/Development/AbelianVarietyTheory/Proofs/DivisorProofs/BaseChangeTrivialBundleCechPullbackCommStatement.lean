module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechPullbackComm
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.baseChangeTrivialBundleCech_pullback_comm : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R'] [Algebra R R''] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X} (w' : φ ≫ s = s' ≫ spMap (algebraMap R R')) (w'' : φ' ≫ s = s'' ≫ spMap (algebraMap R R'')) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X') (wψ : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' → ∀ {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ' ⁻¹ᵁ D i)) (hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i)) (p : ℕ) (z : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p) (t : {s : Finset κ // s.card = p + 1}), Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ z) t = (pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)) (Φ w' D hD' p z t) := by
  first | exact @GlobalTheory.CechPoset.Φ_ext_eq_pullCoef | exact GlobalTheory.CechPoset.Φ_ext_eq_pullCoef | (intros; apply GlobalTheory.CechPoset.Φ_ext_eq_pullCoef <;> assumption)
