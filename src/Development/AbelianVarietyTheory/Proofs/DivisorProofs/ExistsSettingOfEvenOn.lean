module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSquare
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfLevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCpPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitSetting

open GlobalTheory.UU GlobalTheory.LN



theorem exists_setting_of_evenOn (laws : Laws) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (P : CP G) (hS : IsSemiAbelian G) (hE : EvenOn P)
    (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (φ : R →+* V) (hφ : Function.Injective φ)
    (hI : maximalIdeal R ≤ (maximalIdeal V).comap φ) :
    ∃ (A' : PolAV (Sp (FractionRing V))) (s : HidaSetting V A' ((Over.pullback (spMap φ)).obj G)) (w : _),
      IsCPMap s.P P (spMap φ) (pullback.fst G.hom (spMap φ)) pullback.condition w := by
  obtain ⟨X, _, _, _, Q₀, P₀, hlev, hev⟩ := hE
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback _ G hS
  obtain ⟨ψ, sq'⟩ := ClosedPol.exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := ClosedPol.exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  rw [← hP'] at hA'
  obtain ⟨P₀', w₀, H₀⟩ := exists_isLevelCP (maximalIdeal V) 0 P'
  have le : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal V ^ (0 + 1)).comap φ := by
    rw [zero_add, pow_one, pow_one]; exact hI
  let b : R ⧸ maximalIdeal R ^ (0 + 1) →+* V ⧸ maximalIdeal V ^ (0 + 1) := Ideal.quotientMap _ φ le
  have sq : spMap b ≫ thick R (maximalIdeal R) 0 = thick V (maximalIdeal V) 0 ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]
  obtain ⟨wl, hl⟩ := hlev
  obtain ⟨F, pF, w₃, k₃⟩ := ClosedPol.exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G)
    (H := thickObj R (maximalIdeal R) 0 G)
    (H' := thickObj V (maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := P₀) (N' := P₀') sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R (maximalIdeal R) 0))
    (isGrpPullback_pullback _ (thick V (maximalIdeal V) 0)) H hl H₀
  have := hS.smooth
  have := hS.geomConnected
  have : Smooth (thickObj R (maximalIdeal R) 0 G).hom := by
    show Smooth (pullback.snd _ _); infer_instance
  have : GeometricallyConnected (thickObj R (maximalIdeal R) 0 G).hom := by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  obtain ⟨D₀⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ hev
  obtain ⟨Q₀', D₀', -, -, -⟩ := ClosedPol.exists_desc_pull pF Q₀ D₀ k₃
  have ev := UniformizationSetting.exists_even_of_desc D₀'
  obtain ⟨wA, hwA⟩ := hA'
  exact ⟨A', ⟨hV, hG', gen', hgen', P', wA, hwA, _, Q₀', P₀', ⟨w₀, H₀⟩, ev⟩, wP, H⟩

end GlobalTheory.Mum.TraitSetting
end
