module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArchimedeanFrameOfPullbackStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexAbelianFibreAmpleStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsArchimedeanFrameStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinatesStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactorStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FnFactorStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoordinatesUniqueStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroCoordsOfNonzeroVectorStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionDifferentiableStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionUniqueStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionsFiniteDimStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalFormStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformizationDimEqPpDimStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformizationIsoTransferStatement
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameEx

theorem exists_goodUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X)
    (z : Sp ℂ ⟶ X) (t' : SAB H (Sp ℂ)) (m : SABMap t' t z), IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L →
    IsAbelianScheme t'.G ∧ ∃ (g : ℕ) (u : HolUnif t'.G (t.PP.L.pull m.φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
      u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  intro E _ _ _ H X t z t' m hP hA
  have hab : IsAbelianScheme t'.G := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ t'.G hab
  obtain ⟨u₀, hc⟩ := GlobalTheory.T.exists_exp_chart_coordinates t'.G t'.PP.L g hab hA hg
  obtain ⟨u, Hm, χ, hex, hH, hχ, hlaw⟩ := GlobalTheory.T.theta_multiplier_normal_form t'.G t'.PP t'.cub g u₀
  obtain ⟨N, J, Θ, hN, hd, hq, hne, hsep⟩ := GlobalTheory.T.exists_theta_basis_of_factor t'.G t'.PP.L g u Hm χ t'.PP.isLB hab hA hlaw
  have hpos := GlobalTheory.T.theta_functions_finite_dim g u.Λ u.discrete u.full Hm χ N J Θ hH hχ hN hd hq hne hsep
  have hAH : u.IsAH Hm χ := ⟨hH, hpos, hχ, hlaw⟩
  obtain ⟨ht₁, ht₂⟩ := @GlobalTheory.TangentOrigin.tangent_bijection_of_values @GlobalTheory.valAt'_rules t'.G _ t'.PP.L g u
    (by simpa only [hex] using hc)
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  have hL := t'.PP.isLB
  have hM := pull_isLB t.PP.isLB m.φ
  exact ⟨hab, g, GlobalTheory.ArchMetricCompare.carry u hL hM hw₀, Hm, χ, GlobalTheory.ArchMetricCompare.carry_isAH hL hM hw₀ hAH, ht₁, ht₂⟩

end GlobalTheory.CompanionTheory.Ar.Sl.FrameEx


open GlobalTheory.CompanionTheory.Ar.Sl.FrameEx in
theorem GlobalTheory.CompanionTheory.Ar.Sl.frames_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ), Nonempty (D.Frame σ) ∧ ∀ a : D.Frame σ, (∀ (n : ℕ) (s : Out.H0 D.t.PP.L n), ∃! θ, a.IsFn s θ) ∧ (∀ (n : ℕ) (s : Out.H0 D.t.PP.L n) θ, a.IsFn s θ → a.IsTheta n θ) ∧ ∀ x : D.B.carrier, (∃! c, D.IsVec a x c) ∧ ∀ c, D.IsVec a x c → D.len σ x ^ 2 = Real.pi * (a.herm c c).re ∧ (x ≠ 0 → c ≠ 0) := by
  intro E _ _ _ H L _ _ D σ
  obtain ⟨t', m, hP, hA⟩ := GlobalTheory.T.complex_abelian_fibre_ample E H L D σ
  obtain ⟨hab, g, u, Hm, χ, hAH, d₁, d₂⟩ := exists_goodUnif E H _ D.t (emb σ) t' m hP hA
  have hcart : IsGrpPullback t'.G D.t.G (emb σ) m.φ := m.cart
  have hg : D.g = g := GlobalTheory.T.uniformization_dim_eq_pp_dim E H L D σ t'.G m.φ _ g u hcart d₁ d₂
  subst hg
  refine ⟨GlobalTheory.T.exists_archimedean_frame _ D.t.G D.t.PP (emb σ) t'.G m.φ D.g u Hm χ hcart hAH, fun a => ?_⟩
  obtain ⟨e, hmon, -⟩ := grpPullback_iso a.cart hcart
  haveI := hmon
  obtain ⟨a₁, a₂⟩ := GlobalTheory.T.uniformization_iso_transfer t'.G a.A _ _ D.g u a.u e hab d₁ d₂
  refine ⟨fun n s => GlobalTheory.T.theta_function_unique _ D.t.G D.t.PP (emb σ) D.g a n s,
    fun n s θ h => ⟨GlobalTheory.T.theta_function_differentiable _ D.t.G D.t.PP (emb σ) D.g a n s θ h,
      GlobalTheory.T.theta_add_lattice_eq_of_isFn _ D.t.G D.t.PP (emb σ) D.g a n s θ h⟩,
    fun x => ⟨GlobalTheory.T.frame_coordinates_unique E H L D σ a a₁ a₂ x, fun c hc => ?_⟩⟩
  have hl := GlobalTheory.T.archimedean_frame_of_pullback E H L D σ t'.G m.φ D.g u Hm χ hab hcart d₁ d₂ hAH a x c hc
  exact ⟨hl, GlobalTheory.T.nonzero_coords_of_nonzero_vector E H L D σ a x c hl⟩

end
