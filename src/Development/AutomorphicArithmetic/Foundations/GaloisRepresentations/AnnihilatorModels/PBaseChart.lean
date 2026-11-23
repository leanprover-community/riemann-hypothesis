module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.baseChart_of :
    BaseOfSmooth → BaseOfChart := by
  intro h
  unfold BaseOfChart
  intro l O _ _ _ ϖ hϖ hl hlu Y g hg U hU
  let φ : O →+* Γ(Y, U) :=
    (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hφ : ∀ a : O, φ a = (Y.presheaf.map (homOfLE le_top).op).hom
      ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) := fun a => rfl
  have hsm : φ.Smooth := by
    refine RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_
    · exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv)
    · exact HasRingHomProperty.appLE @Smooth g hg ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  letI : Algebra O Γ(Y, U) := φ.toAlgebra
  haveI : Algebra.Smooth O Γ(Y, U) := hsm
  have hb := h l O Γ(Y, U) ϖ hϖ hl hlu
  have hϖφ : (algebraMap O Γ(Y, U)) ϖ = (Y.presheaf.map (homOfLE le_top).op).hom (fn g ϖ) := hφ ϖ
  rw [hϖφ] at hb
  refine ⟨hb, 1, ?_⟩
  have hmem : (l : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hlu
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [pow_one, ← hϖφ, Ideal.mem_span_singleton']
  refine ⟨algebraMap O Γ(Y, U) c, ?_⟩
  rw [← map_mul, hc, map_natCast]
