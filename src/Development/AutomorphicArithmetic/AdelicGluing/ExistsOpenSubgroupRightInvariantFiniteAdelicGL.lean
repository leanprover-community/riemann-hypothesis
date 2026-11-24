module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
import GroundTheory.AutomorphicForms.SphericalLaurent

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem locally_constant_right_invariant_open_subgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G)) [CompactSpace K₀] [TotallyDisconnectedSpace K₀]
    (e : G → ℂ) (he : IsLocallyConstant e) (hc : HasCompactSupport e) :
    ∃ W : Subgroup G, IsOpen (W : Set G) ∧ ∀ k ∈ W, ∀ x, e (x * k) = e x := by
  letI : Inv (Set G) := Set.inv
  have hF : IsLocallyConstant fun p : G × G => e (p.1 * p.2) - e p.1 :=
    (he.comp_continuous (continuous_fst.mul continuous_snd)).sub (he.comp_continuous continuous_fst)
  have hN : IsOpen {p : G × G | e (p.1 * p.2) - e p.1 = 0} := hF.isOpen_fiber 0
  obtain ⟨A, V, -, hVo, hCA, h1V, hAV⟩ := generalized_tube_lemma (s := tsupport e) hc
    (isCompact_singleton (x := (1 : G))) hN (by
      rintro ⟨x, k⟩ ⟨-, hk⟩
      have hk' : k = 1 := hk
      simp [hk'])
  have h1 : (1 : G) ∈ V := h1V rfl
  have hinv : ∀ x ∈ tsupport e, ∀ k ∈ V, e (x * k) = e x :=
    fun x hx k hk => sub_eq_zero.1 (hAV (Set.mk_mem_prod (hCA hx) hk))
  have hVi : IsOpen (V ∩ V⁻¹) := hVo.inter hVo.inv
  have hUo : IsOpen ((↑) ⁻¹' (V ∩ V⁻¹) : Set K₀) := hVi.preimage continuous_subtype_val
  have hU1 : (1 : K₀) ∈ ((↑) ⁻¹' (V ∩ V⁻¹) : Set K₀) := by
    simp [h1]
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo hU1
  refine ⟨(H.toOpenSubgroup.toSubgroup).map K₀.subtype, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact hK.isOpenEmbedding_subtypeVal.isOpenMap _ H.toOpenSubgroup.isOpen
  · rintro _ ⟨u, hu, rfl⟩ x
    have hV : (u : G) ∈ V ∩ V⁻¹ := hH hu
    by_cases hx : x ∈ tsupport e
    · exact hinv x hx _ hV.1
    by_cases hxk : x * u ∈ tsupport e
    · have := hinv _ hxk _ hV.2
      simpa using this.symm
    · change e (x * u) = e x
      rw [image_eq_zero_of_notMem_tsupport hxk, image_eq_zero_of_notMem_tsupport hx]

theorem UpperTheory.exists_open_subgroup_rightInvariant_finiteAdelicGL :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (e : TF K n), IsLocallyConstant e →
      ∃ W : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (W : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ ∀ k ∈ W, ∀ x, e (x * k) = e x := by
  intro K _ _ n e he
  exact locally_constant_right_invariant_open_subgroup (AdelicGLn.integralFiniteGL K n) (AdelicGLn.isOpen_integralFiniteGL K n) e he e.hasCompactSupport
