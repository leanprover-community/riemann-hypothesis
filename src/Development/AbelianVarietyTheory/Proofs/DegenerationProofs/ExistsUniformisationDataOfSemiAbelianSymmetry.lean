module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetryHypExtendsSemiAbelianDvrStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationSpecialFibreStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenOfChartPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianAndTqOfIsGt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveAppTopOfInjective
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem exists_setting_of_hypS : Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj G)) → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∃ s : GlobalTheory.UU.HidaSetting V A G, s.gen = gen := by
  intro laws hext V _ _ hd _ hc A G _ _ hG hE hS gen hgen
  have hV : GlobalTheory.UU.CDVR V := ⟨hd, hc, inferInstance⟩
  obtain ⟨L, hL⟩ := GlobalTheory.UU.polarisation_extends laws V A G hG gen hgen
  obtain ⟨P, rfl⟩ := GlobalTheory.CubicalPackage.exists_package laws V hV A G hG gen hgen L hL
  obtain ⟨w, -, hw, -, -, hiso, -⟩ := GlobalTheory.T.symmetryHyp_extends_semiAbelian_dvr hext V A G hG hS gen hgen P.L hL
  obtain ⟨E, ⟨d⟩⟩ := hE
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue V))).obj G) := Functor.isCommMonObj_obj
  obtain ⟨r, hr⟩ := GlobalTheory.UU.thick_zero_factor V
  obtain ⟨Q₀⟩ := GlobalTheory.UU.nonempty_tq_pullback_comp r _ hr G (GlobalTheory.UU.TQ.ofGtDatum d)
  obtain ⟨P₀, h₀⟩ := GlobalTheory.UU.exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P
  obtain ⟨wA, hwA⟩ := hL
  have := E.free
  have := E.finite
  exact ⟨⟨hV, hG, gen, hgen, P, wA, hwA, E.X, Q₀, P₀, h₀,
    GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre laws V hV A G hG gen hgen P w hw hiso E.X Q₀ P₀ h₀⟩, rfl⟩

end GlobalTheory.ZH
