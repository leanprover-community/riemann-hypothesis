module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisRowsHaveClassWeightStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisSectionsModKStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleAdaptedBasisLinkMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestLatticeEqSpanModelSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelAdaptedBasisIsModelWithSeriesStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.GeoExist

theorem link_smul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ}
    [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (σ : S.J → (u.H S.N).Sec)
    (b : Matrix S.J S.J (FractionRing u.V)) (h : u.Link σ b) (c : FractionRing u.V) (hc : c ≠ 0) :
    u.Link σ (c • b) := by
  intro a v hv
  have hc' : algebraMap (FractionRing u.V) (PadicAlgCl p) c ≠ 0 := (map_ne_zero _).2 hc
  have h₁ := CrdCalc.crd_smul (Units.mk0 _ hc') (h a v hv)
  convert h₁ using 1
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, _root_.mul_assoc]

theorem hasGeo_of_hasU : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ρ.HasU → ρ.HasGeo := by
  intro hL hT o Ω _ _ _ _ S ρ hB hU p _ y₀ hy Fs
  obtain ⟨u, l, τ, hm, hF⟩ := hU p y₀ hy Fs
  obtain ⟨σ, cls, f, hb⟩ := GlobalTheory.T.exists_adapted_basis_sections_mod_k hL o Ω S ρ p y₀ u l S.N (le_trans one_le_two S.N_ge) S.J ρ.card
  obtain ⟨md⟩ := GlobalTheory.T.uniformisedModel_adaptedBasis_is_modelWithSeries hL hT o Ω S ρ p y₀ u l σ cls f hb
  obtain ⟨b, hd, hl⟩ := GlobalTheory.T.exists_invertible_adaptedBasis_link_matrix hL o Ω S ρ p y₀ u l σ cls f hb
  obtain ⟨c, hc, hs⟩ := GlobalTheory.T.testLattice_eq_span_model_sections hL o Ω S ρ p y₀ u l τ σ cls md b hB hy hm hl hd
  have hl' := link_smul u σ b hl c hc
  exact ⟨⟨u, l, τ, hm, σ, cls, md, c • b, hl', hs,
    GlobalTheory.T.adaptedBasis_rows_have_class_weight hL hT o Ω S ρ p y₀ u l σ cls f hb (c • b) hl'⟩, hF⟩

end GlobalTheory.ZH.GeoExist
