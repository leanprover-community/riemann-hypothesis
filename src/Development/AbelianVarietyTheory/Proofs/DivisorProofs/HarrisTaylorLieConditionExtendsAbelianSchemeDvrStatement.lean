module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionExtendsAbelianSchemeDvr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_extends_abelianScheme_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (ρ : W) (t : Fin D.a → (𝓞 D.F →+* W)), (∀ i, t i D.ω = ρ) → ρ ^ 2 - D.tr * ρ + D.nm = 0 → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((D.tr ^ 2 - 4 * D.nm : ℤ) : W) → (∀ (R' : Type) [CommRing R'] (β : L →+* R'), ∀ v : epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O D.ω) (β (algebraMap W L ρ)) v → ∃ w : Fin D.a → (epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O c) (β (algebraMap W L (t i c))) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k) i, LieMult (act.toF D) (spMap (β.comp (algebraMap W L))) ((β.comp (algebraMap W L)).comp (t i)) D.m) → (∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∀ v : epsPtR (spMap β) ⟶ G, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O D.ω) (β ρ) v → ∃ w : Fin D.a → (epsPtR (spMap β) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) (β (t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k) i, LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m := by
  first | exact @GlobalTheory.LieExt.lie_ext | exact GlobalTheory.LieExt.lie_ext | (intros; apply GlobalTheory.LieExt.lie_ext <;> assumption)
