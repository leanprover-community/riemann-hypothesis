module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

theorem val_eq_of_spMap : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (Rs : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp Rs), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap Rs.val.toRingHom) → ∀ (K : Type) [Field K] (q : Sp K ⟶ U₀.toScheme) (f : Rs →+* K), spMap f = q ≫ u₀ → ∀ a : Rs, M.val (q ≫ U₀.ι) (a : Ω) = f a := by
  intro o Ω _ _ _ M U₀ Rs u₀ hne hpt K _ q f hf a
  set s : Γ(U₀.toScheme, ⊤) :=
    (u₀.appLE ⊤ ⊤ (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of Rs)).inv.hom a) with hs
  set t : Γ(M.Z, U₀.ι ''ᵁ ⊤) := (U₀.ι.appIso ⊤).inv.hom s with ht
  have key : ∀ {C : Type} [Field C] (y : Sp C ⟶ U₀.toScheme),
      valF (y ≫ U₀.ι) (U₀.ι ''ᵁ ⊤) t = valR (y ≫ u₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Rs)).inv.hom a) := by
    intro C _ y
    rw [GlobalTheory.Points.valF_eq_valR, ← GlobalTheory.Points.valR_appLE y U₀.ι (U₀.ι.preimage_image_eq ⊤).ge
      (GlobalTheory.Points.le_preimage_top y), ← Scheme.Hom.appIso_hom', ht, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply, hs]
    exact GlobalTheory.Points.valR_appLE y u₀ _ (GlobalTheory.Points.le_preimage_top y) _
  have hW : ∀ {C : Type} [Field C] (y : Sp C ⟶ U₀.toScheme),
      Set.range (y ≫ U₀.ι) ⊆ ((U₀.ι ''ᵁ ⊤ : M.Z.Opens) : Set M.Z) := by
    intro C _ y
    rw [Scheme.Opens.ι_image_top, ← Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ⟨y w, rfl⟩
  have hrange : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact M.top_le_preimage_pt hne (x := w) trivial
  have hx : IsOpenImmersion.lift U₀.ι M.pt hrange ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have h1 := hpt _ hx
  have e1 : valF M.pt (U₀.ι ''ᵁ ⊤) t = (a : Ω) := by
    rw [← hx, key, h1, GlobalTheory.Points.valR_specMap]
    rfl
  rw [RatModel.val_eq (hW q) e1, key, ← hf, GlobalTheory.Points.valR_specMap]
  rfl

end GlobalTheory.Poinc.TestAtPt
